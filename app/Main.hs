module Main where

import TrackerLib

storages :: Storages
storages = Storages {
    messages=DBName "messages.kch"   -- Hashes
  , murmurs=DBName "murmurs.kch"
  , taxonomy=DBName "taxonomy.kch"
  , registryDates=DBName "dates.kct" -- Tree
  , basePath="/var/tmp/"}

main :: IO ()
main = do
  msgServer storages
