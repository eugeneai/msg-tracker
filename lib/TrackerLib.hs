{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}

module TrackerLib (msgServer) where

import Web.Scotty
import Network.Wai.Middleware.RequestLogger (logStdout, logStdoutDev)
import Network.Wai.Middleware.Static
-- import qualified Data.Text.Internal.Lazy as T
import qualified Data.Text as T
import qualified Data.ByteString.Lazy.Char8 as BL
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

data Message = Answer
               {  id::U.UUID
               -- , lev::Float
               , mm::MM.Hash64
               } deriving (Show, Eq, Generic)

instance FromJSON Message

instance FromJSON MM.Hash64 where

  parseJSON (String v) = case pp of
                           Just uuid -> CA.pure . toHash $ uuid
                           Nothing -> CA.empty
    where
      pp = U.fromText v
  parseJSON _ = CA.empty

instance ToJSON Message

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

msgServer :: IO ()
msgServer = scotty 3333 $ do
  middleware $ staticPolicy (noDots >-> addBase "static")
-- Логирование всех запросов. Для продакшена используйте logStdout вместо logStdoutDev
  middleware $ logStdoutDev -- logStdout
--  middleware $ basicAuth (verifyCredentials pool)
--    "Haskell Blog Realm" { authIsProtected = protectedResources }
  get "/test/:word" $ do
    beam <- param "word"
    html $ mconcat ["<h1>Scotty, ", beam, " me up!!!</h1>"]

  -- Create new message an classify it, returning UUID and class
  post "/messages/" $ do
    b <- body
    muuid <- liftIO $ UU.nextUUID
    case muuid of
      Just uuid -> do
        let answer = Answer {id=uuid, mm=MM.hash64 b}
        -- html $ mconcat ["<pre>", (TLE.decodeUtf8 b), "</pre>", "/n", maybe "" (TL.fromStrict . U.toText) muuid]
        -- html $ mconcat ["<pre>", (TLE.decodeUtf8 b), "</pre>", "/n", maybe "" (TL.fromStrict . U.toText) muuid]
        json answer

      Nothing -> json ()
