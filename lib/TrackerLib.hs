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
import qualified Data.UUID.V1 as UU
import Control.Monad.IO.Class
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
-- import Data.Aeson
import Prelude.Compat
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

data Message = Answer
               {  id::U.UUID
               -- , lev::Float
               , mm::MM.Hash64
               -- , error::T.Text
               } deriving (Show, Eq, Generic)

data ErrorReport = Error
                 {
                   description :: T.Text
                 , subsys:: T.Text
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
    put "/messages/" $ do
      b <- body
      muuid <- liftIO $ UU.nextUUID
      case muuid of
        Just uuid -> do
          krc <- liftIO $ storeMessage db uuid b
          case krc of
            KKOK -> do
              let answer = Answer {id=uuid, mm=MM.hash64 b}
              json answer
            KKError e -> json $ Error {description=T.pack e, subsys="kyotocabinet"}

        Nothing -> json $ Error {
          description="Cannot generate an UUID",
          subsys="message saving"}

data KKResult = KKOK | KKError String deriving Show

uuidToBS :: U.UUID -> BS.ByteString
uuidToBS = BL.toStrict . U.toByteString

mmToBS :: MM.Hash64 -> BS.ByteString
mmToBS = BS.pack . show . MM.asWord64

storeMessage :: Storages -> U.UUID -> BL.ByteString -> IO KKResult
storeMessage sto uuid msg = do
  K.set (db $ messages sto) k (BL.toStrict msg)
  return KKOK
  where
    k = BL.toStrict . U.toByteString $ uuid

storeMurMur :: Storages -> MM.Hash64 -> U.UUID -> IO ()
storeMurMur sto mm uuid =
  K.set (db $ murmurs sto) k uu
  where
    k = mmToBS mm
    uu = uuidToBS uuid

checkMurMur :: Storages -> MM.Hash64 -> IO (Maybe BS.ByteString)
checkMurMur sto mm = do
  K.get (db $ murmurs sto) k
  where
    k = mmToBS mm
