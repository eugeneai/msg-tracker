{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}

module TrackerLib (msgServer, Storages(..), DB(..)) where

import Web.Scotty
import Network.Wai.Middleware.RequestLogger (logStdout, logStdoutDev)
import Network.Wai.Middleware.Static
-- import qualified Data.Text.Internal.Lazy as T
import qualified Data.Text as T
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.ByteString.Char8 as BS
import Data.Text.Lazy.Encoding    as TLE

import qualified Data.UUID as U
import qualified Data.UUID.V1 as U
import Control.Monad.IO.Class
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
-- https://gist.github.com/dino-/28b09c465c756c44b2c91d777408e166
import qualified Data.Text.Lazy as TL
import Data.Ratio (Ratio, numerator, denominator, (%))
import GHC.Float.RealFracMethods (roundFloatInt)
import Data.List (elem)
import TLSH (tlshHash
            , tlshUpdate
            , tlshFinalize
            , tlshDigest
            )
-- import Data.Aeson
import Prelude.Compat
    ( (++),
      ($),
      Eq,
      Monad(return),
      Show(show),
      Monoid(mconcat),
      String,
      Maybe(..),
      IO,
      Either(..),
      maybe,
      snd,
      (.),
      id,
      (*), (/), map,
      FilePath, putStrLn, Float, Int, Integer,
      fromIntegral)
import GHC.Generics (Generic)
import qualified Control.Monad.Extra as Ex
import Web.Scotty
import Data.Aeson.Types ( FromJSON(..), Value(String), ToJSON(..) )
-- import Data.Aeson (FromJSON(..))
import qualified Data.Digest.Murmur64 as MM
import Data.Digest.Murmur64 (asWord64)
import qualified Data.Text.Metrics as Met
import qualified Control.Applicative as CA
import qualified Database.KyotoCabinet.DB.Hash as K
import qualified Database.KyotoCabinet.DB.Tree as K
import qualified Database.KyotoCabinet.Operations as K
import qualified Data.Array.Byte as BL
import qualified Data.Aeson.Key as BL
import Network.Email.Mailbox (MailboxReader(getMessages))
import Network.Stream (ConnError(ErrorReset))
import qualified Data.UUID as TL
import NumHask (fromRatio)
import Foreign (IntPtr(IntPtr))

data Message = Answer
               {  msgid::U.UUID
               -- , lev::Float
               , mm::U.UUID -- MM.Hash64 as UUID = 0.....0-hash
               -- , error::T.Text
               , tlsh::String
               } deriving (Show, Eq, Generic)

data ErrorReport = Error
                 { error :: T.Text
                 , description :: T.Text
                 , subsys:: T.Text
                 } deriving (Show, Eq, Generic)

data Metric = Metric { mtype :: String -- Type of metric
                     , msg :: [U.UUID]
                     , value :: Int
                     } deriving (Show, Eq, Generic)

instance FromJSON Message
instance FromJSON ErrorReport

instance FromJSON MM.Hash64 where

  parseJSON (String v) = case pp of
                           Just uuid -> CA.pure . toHash $ uuid
                           Nothing -> CA.empty
    where
      pp = U.fromText v
  parseJSON _ = CA.empty

instance ToJSON Message
instance ToJSON ErrorReport
instance ToJSON Metric

instance ToJSON MM.Hash64 where
  toJSON :: MM.Hash64 -> Value
  toJSON = String . U.toText . fromHash

fromHash :: MM.Hash64 -> U.UUID
fromHash = U.fromWords64 0 . MM.asWord64

toHash :: U.UUID -> MM.Hash64
toHash uuid = MM.hash64AddWord64 (snd rc) h0
  where
    rc = U.toWords64 uuid
    h0 = MM.hash64 BL.empty


data DB db = DB {db::db} | DBName String

data Storages = Storages
                {
                  messages :: DB K.Hash
                , murmurs :: DB K.Hash
                , taxonomy :: DB K.Hash
                , registryDates :: DB K.Tree
                , basePath :: FilePath
                }

instance Parsable U.UUID where
  parseParam :: TL.Text -> Either TL.Text U.UUID
  parseParam t = case U.fromText . TL.toStrict $ t of
                   Nothing -> Left "param not an UUID"
                   Just uuid -> Right uuid

openHashDB :: FilePath -> DB db -> IO K.Hash
openHashDB basePath (DBName name) = do
  let pathName = basePath ++ name
  K.makeHash pathName K.defaultLoggingOptions K.defaultHashOptions (K.Writer [K.Create] [])

openTreeDB :: FilePath -> DB db -> IO K.Tree
openTreeDB basePath (DBName name) = do
  let pathName = basePath ++ name
  K.makeTree pathName K.defaultLoggingOptions K.defaultTreeOptions (K.Writer [K.Create] [])

openDatabases :: Storages -> IO Storages
openDatabases sto = do
  let bp = basePath sto
  let oht = openHashDB bp
      ott = openTreeDB bp
  messages <- oht $ messages sto
  murmurs <- oht $ murmurs sto
  taxonomy <- oht $ taxonomy sto
  registryDates <- ott $ registryDates sto

  return $ Storages {
      messages=DB messages
    , murmurs=DB murmurs
    , taxonomy=DB taxonomy
    , registryDates=DB registryDates
    , basePath = bp}

msgServer :: Storages -> IO ()
msgServer sto = do
  db <- openDatabases sto
  scotty 3333 $ do
    middleware $ staticPolicy (noDots >-> addBase "static")
    -- Логирование всех запросов. Для продакшена используйте logStdout вместо logStdoutDev
    middleware $ logStdout
    --  middleware $ logStdoutDev
    --  middleware $ basicAuth (verifyCredentials pool)
    get "/test/:word" $ do
      beam <- param "word"
      html $ mconcat ["<h1>Scotty, ", beam, " me up!!!</h1>"]

    -- Create new message an classify it, returning UUID and class
    -- PUT --------------------------------------------
    put "/api-1.0/messages/" $ do
      b <- body
      let mm = fromHash . MM.hash64 $ b
      -- liftIO $ putStrLn $ "Cmurmur" ++ show mm
      cmm <- liftIO $ getMurMur db mm
      let tlsh = tlshHash b
          tlshD = tlshDigest tlsh :: String
      -- liftIO $ putStrLn $ show $ BL.length b
      liftIO $ putStrLn $ "TLSH: " ++ show tlsh
      liftIO $ putStrLn $ "TLSH digest: " ++ (show $ (tlshD))
      case cmm of
        Just uuid -> do
          json $ Error { error = "mm-exists",
                         description="There is such message",
                         subsys= "storage"}
        Nothing -> do
          muuid <- liftIO $ U.nextUUID
          case muuid of
            Just uuid -> do
              krc <- liftIO $ storeMessage db uuid b
              mmrc <- liftIO $ storeMurMur db mm uuid
              let answer = Answer {msgid=uuid, mm=mm, tlsh=tlshD}
              json answer
            Nothing -> json $ Error {error="no-uuid",
                                     description="Cannot generate an UUID",
                                     subsys="server"}

    -- GET --------------------------------------------
    get "/api-1.0/message/uuid/:uuid" $ do
      uuid <- param $ "uuid"
      mtxt <- liftIO $ getMessage db uuid
      case mtxt of
        Nothing -> json $ Error {error="no-message",
                                 description="There are no such message",
                                 subsys="storage"}
        Just msg -> raw . BL.fromStrict $ msg

    -- GET --------------------------------------------
    get "/api-1.0/message/mm/:mm" $ do
      uuid <- param $ "mm"
      mmm <- liftIO $ getMurMur db $ uuid
      case mmm of
        Nothing -> do json $ Error {error="no-message",
                           description="There are no such message",
                           subsys="storage"}
        Just uuid -> do
          mtxt <- liftIO $ getMessage db uuid
          case mtxt of
            Nothing -> json $ Error {error="no-message",
                                     description="Murmur has found, but uuid not",
                                     subsys="storage"}
            Just msg -> raw . BL.fromStrict $ msg

    -- GET ---------------------------------------------
    get "/api-1.0/:metric/:uuid1/:uuid2" $ do
      uuid1 <- param "uuid1"
      uuid2 <- param "uuid2"
      met <- param "metric"
      msg1 <- liftIO $ getMessage db uuid1
      msg2 <- liftIO $ getMessage db uuid2
      if met `elem` (map T.pack $ ["lev", "jaro", "jaccard"]) then
        case msg1 of
          Nothing -> do json $ err ("first" :: String)
          Just mes1 -> do
            case msg2 of
              Nothing -> do json $ err ("second" :: String)
              Just mes2 -> do
                let val = case T.unpack met of
                      "lev" -> (lnorm mes1 mes2) :: Ratio Int
                      "jaro" -> (jnorm mes1 mes2) :: Ratio Int
                      "jaccard" -> (janorm mes1 mes2) :: Ratio Int
                      _ -> 0 % 0 :: Ratio Int
                json $ Metric {mtype=T.unpack met, msg=[uuid1, uuid2], value=fromRatio_ val }
      else json $ Error {description="Unknown metric", subsys="server", error="no-metric"}
    where
      fromRatio_ :: Ratio Int -> Int
      fromRatio_ r = roundFloatInt $ 100 * ((fromIntegral $ numerator r) /
                                            (fromIntegral $ denominator r))
      lnorm :: BS.ByteString -> BS.ByteString -> Ratio Int
      lnorm a b = Met.levenshteinNorm (cnv a) (cnv b)
      jnorm a b = Met.jaro (cnv a) (cnv b)
      janorm a b = Met.jaccard (cnv a) (cnv b)
      cnv = T.decodeUtf8
      err :: String -> ErrorReport
      err p = Error {subsys="storage",
                     description=T.pack $ mconcat
                      ["No message identified by the ", p, " UUID"],
                     error="no-message"}


data KKResult = KKOK | KKError String deriving Show

uuidToBS :: U.UUID -> BS.ByteString
uuidToBS = BL.toStrict . U.toByteString

mmToBS :: MM.Hash64 -> BS.ByteString
mmToBS = BS.pack . show . MM.asWord64

storeMessage :: Storages -> U.UUID -> BL.ByteString -> IO ()
storeMessage sto uuid msg = do
  K.set (db $ messages sto) k (BL.toStrict msg)
  where
    k = BL.toStrict . U.toByteString $ uuid

getMessage :: Storages -> U.UUID -> IO (Maybe BS.ByteString)
getMessage sto uuid = do
  K.get (db $ messages sto) k
  where k = uuidToBS uuid

storeMurMur :: Storages -> U.UUID -> U.UUID -> IO ()
storeMurMur sto mm uuid =
  K.set (db $ murmurs sto) k uu
  where
    k = uuidToBS mm
    uu = uuidToBS uuid

getMurMur :: Storages -> U.UUID -> IO (Maybe U.UUID)
getMurMur sto mm = do
  uuidStr <- K.get (db $ murmurs sto) k
  -- liftIO $ putStrLn $ "uuidStr" ++ show uuidStr
  return $ U.fromByteString . maybe "" BL.fromStrict $ uuidStr
  where
    k = uuidToBS mm
