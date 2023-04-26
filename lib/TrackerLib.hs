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
import Data.Aeson.Types

data Message = Answer
               {  id::U.UUID
               -- , lev::Float
               , hash::Int
               } deriving (Show, Eq, Generic)

instance FromJSON Message
instance ToJSON Message

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
        let answer = Answer {id=uuid, hash=32}
        -- html $ mconcat ["<pre>", (TLE.decodeUtf8 b), "</pre>", "/n", maybe "" (TL.fromStrict . U.toText) muuid]
        -- html $ mconcat ["<pre>", (TLE.decodeUtf8 b), "</pre>", "/n", maybe "" (TL.fromStrict . U.toText) muuid]
        json answer

      Nothing -> json ()
