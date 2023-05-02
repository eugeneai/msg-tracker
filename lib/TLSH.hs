{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}

module TLSH
  (
    tlshInit
  , tlshUpdate
  , tlshFinalize
  , tlshHash
  , tlshDigest
  )
  where

import Prelude.Compat
import Data.Bits ( Bits(..) )
import Data.Vector
import qualified Data.Vector as V
import qualified Data.Vector.Algorithms.Quicksort as Q
import qualified Data.Vector.Mutable as M
-- import Data.Text.Lazy as TL
import Data.Int (Int8, Int16, Int32, Int64)
import qualified Data.ByteArray as BA
import GHC.Integer (xorInteger)
import Data.Word8 (Word8)
import Data.Char ( ord )
import qualified Data.List as L
import GHC.Float.RealFracMethods (floorFloatInt)
import Data.Text.Internal.Read (hexDigitToInt)
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.ByteString.Lazy.Char8 as BL
import Data.Aeson.Decoding.ByteString (bsToTokens)
import Control.Monad.ST (ST, runST)
import qualified Data.Vector.Unboxed as U
import qualified Data.Text as TL
-- import Data.Hex

type Bucket = Vector Word8

data TlshContext = Tc { bucket :: Bucket
                      , qs :: [Word8]
                      , checksum :: Int
                      , bytesLen :: Int
                      , word8Header :: Bucket
                      , word8Digest :: Bucket
                      }

instance Show TlshContext where
  show :: TlshContext -> String
  show (Tc bu qs ch bl wh dg) = L.concat [showBu bu,
                                    " ", (show qs), " / ", (show ch),
                                    " | ", show bl, " | ",
                                    " / ", showBu wh,
                                    " / ", showBu dg]

showBu :: Vector Word8 -> String
showBu bu =
  let s = V.foldr fbu "" bu
  in s
  where
    fbu :: Word8 -> String -> String
    fbu e s = L.concat [show e, ", ", s]

instance Eq TlshContext where
  (==) :: TlshContext -> TlshContext -> Bool
  (==) a b = (bucket a) == (bucket b)

data Tlsh = Tlsh TlshContext
          deriving (Show, Eq)

hashBlockSize :: Int
hashBlockSize = 5

tlshInit :: TlshContext
tlshInit = Tc { bucket = zeroVector buckets,
                qs = [0,0,0], checksum = 0,
                bytesLen = 0,
                word8Header = zeroVector int_digest_header,
                word8Digest = zeroVector int_digest_length}

zeroVector size = (V.replicate size 0)

tlshUpdate :: TlshContext -> ByteString -> TlshContext
tlshUpdate context byteString =
  let tmp = L.foldl updateGo context
                    (zipg hashBlockSize byteString) :: TlshContext
  in updateChecksum tmp
  where
    zipg :: Int -> BL.ByteString -> [BL.ByteString]
    zipg n bs = L.filter (\str -> BL.length str == (toEnum n)) $ zipg' n bs
    zipg' :: Int -> BL.ByteString -> [BL.ByteString]
    zipg' n bs = (BL.take (toEnum n) bs):restGo n bs

    restGo :: Int -> BL.ByteString -> [BL.ByteString]
    restGo n bs =
      let
        tryN = BL.take (toEnum n) bs
      in if BL.length tryN /= 0 then zipg' n $ BL.tail bs else []

    updateChecksum ctx = ctx

    updateGo :: TlshContext -> BL.ByteString -> TlshContext
    updateGo c bs = do
      let b = bucket c
      let lc = toString bs
      let ubu = L.foldr (upd lc) b [1..6]
      let ncs = BL.foldr (\x prev -> prev + (fromEnum . ord $ x)) -- TODO: Check alg
                         (checksum c) bs
      Tc {bucket = ubu, qs = (qs c), checksum=ncs,
          bytesLen = (bytesLen c) + fromEnum (BL.length bs),
          word8Header = (word8Header c),
          word8Digest=(word8Digest c)}

    upd :: [Char] -> Int -> Bucket -> Bucket
    upd lc i b = V.modify (\el -> M.modify el (\v -> v+1)
                                  (triplet hashBlockSize lc i)) b

    triplet :: Int -> [Char] -> Int -> Int
    triplet 5 [b0,b1,b2,b3,b4] 1 = bMapping 49  b0 b1 b2
    triplet 5 [b0,b1,b2,b3,b4] 2 = bMapping 12  b0 b1 b3
    triplet 5 [b0,b1,b2,b3,b4] 3 = bMapping 178 b0 b2 b3
    triplet 5 [b0,b1,b2,b3,b4] 4 = bMapping 166 b0 b2 b4
    triplet 5 [b0,b1,b2,b3,b4] 5 = bMapping 84  b0 b1 b4
    triplet 5 [b0,b1,b2,b3,b4] 6 = bMapping 230 b0 b3 b3
    triplet _ _ _ = error "Hashing scheme is not implemented"

    toString = BL.unpack

tlshFinalize :: TlshContext -> TlshContext
tlshFinalize ctx =
  let sbu = sortGo . bucket $ ctx
      q = calcQuartiles sbu
      (wh3, digest) = calcDigest ctx q
  in Tc {bucket = (bucket ctx), qs=q, checksum=(checksum ctx),
         bytesLen = (bytesLen ctx),
         word8Header = wh3,
         word8Digest = digest}
  where
    -- qCalc q q3 = toEnum ((floorFloatInt(fromIntegral (q*100) /
    --                                     fromIntegral q3)) `mod` 16) :: Word8
    qCalc q q3 = (((q*100) `div` q3) `mod` 16)
    calcDigest ctx q =
      let bu = bucket ctx
          cs = checksum ctx
          wh = word8Header ctx
          wd = word8Digest ctx
          logOfLen = toEnum $ ((lCapturing . bytesLen $ ctx) `mod` 256) :: Word8
          qh = qCalc (q !! 0) (q !! 2)
          ql = qCalc (q !! 1) (q !! 2)
          qd = (shiftL qh 4) .|. ql -- or wise versa
      in
        let wh1 = V.modify (\el -> M.write el 0 (toEnum $ cs `mod` 256)) wh
            wh2 = V.modify (\el -> M.write el 1 logOfLen) wh1
            wh3 = V.modify (\el -> M.write el 2 qd) wh2
            wdend = fillFromBucket q bu wd 0 0
        in (wh3, wdend)

    fillFromBucket :: [Word8] -> Bucket -> Bucket -> Int -> Int -> Bucket
    fillFromBucket q bu wd iwd ibu =
      let val = emit q [(bu ! ibu), (bu ! (ibu+1)), (bu ! (ibu+3)), (bu ! (ibu+2))]
          wd1 = V.modify (\el -> M.write el iwd val) wd
      in if ibu + 4 < V.length bu
         then fillFromBucket q bu wd1 (iwd+1) (ibu+4)
         else wd1

    emit :: [Word8] -> [Word8] -> Word8
    emit q = L.foldl (\acc x -> (shiftL acc 2) + (qual q x)) 0
      where
        qual :: [Word8] -> Word8 -> Word8
        qual [q1, q2, q3] v
          | v <= q1 = 0
          | v <= q2 = 1
          | v <= q3 = 2
          | otherwise = 3

    calcQuartiles:: Bucket -> [Word8]
    calcQuartiles bu = [bv bu 4 1, bv bu 2 1, bv bu 4 3]
    idxs len divider mult
      | len `mod` divider == 0 =
        let d = len `div` divider
            p = d*mult in [p,p+1]
      | otherwise =
        let d = len `div` divider
            p = d*mult in [p+1]
    bv :: Bucket -> Int -> Int -> Word8
    bv bu d m =
      let ids = idxs buckets d m
      in case ids of
           [i] -> bu ! i
           [i,j] -> let s = (bu ! i) + (bu ! j)
                    in (shiftR s 1) + if even s then 0 else 1

    sortGo :: Bucket -> Bucket
    sortGo b = Q.sort $ b

class HexDigest a where
  tlshDigest :: TlshContext -> a

instance HexDigest [Char] where
  tlshDigest ctx =
    let hwh = toHex . word8Header $ ctx
        wd = word8Digest ctx
    in L.concat [hwh, toHex wd]
    where
      toHex = V.foldr th ""
      th :: Word8 -> [Char] -> [Char]
      th b str =
        let a = tt (shiftR b 4 :: Word8)
            c = tt (b .&. 0x0f :: Word8)
        in a:c:str

      tt :: Word8 -> Char
      tt 0 = '0'
      tt 1 = '1'
      tt 2 = '2'
      tt 3 = '3'
      tt 4 = '4'
      tt 5 = '5'
      tt 6 = '6'
      tt 7 = '7'
      tt 8 = '8'
      tt 9 = '9'
      tt 10 = 'A'
      tt 11 = 'B'
      tt 12 = 'C'
      tt 13 = 'D'
      tt 14 = 'E'
      tt 15 = 'F'

instance HexDigest BL.ByteString where
  tlshDigest ctx =
    let hd = tlshDigest ctx :: String
    in BL.pack hd

instance HexDigest TL.Text where
  tlshDigest ctx =
    let hd = tlshDigest ctx :: String
    in TL.pack hd

tlshHash :: ByteString -> TlshContext
tlshHash bs =
  let tlsh = tlshInit
      tlsh1 = tlshUpdate tlsh bs
      answer = tlshFinalize tlsh1
  in answer

vTable :: Vector Word8
vTable = fromList [
    1, 87, 49, 12, 176, 178, 102, 166, 121, 193, 6, 84, 249, 230, 44, 163,
    14, 197, 213, 181, 161, 85, 218, 80, 64, 239, 24, 226, 236, 142, 38, 200,
    110, 177, 104, 103, 141, 253, 255, 50, 77, 101, 81, 18, 45, 96, 31, 222,
    25, 107, 190, 70, 86, 237, 240, 34, 72, 242, 20, 214, 244, 227, 149, 235,
    97, 234, 57, 22, 60, 250, 82, 175, 208, 5, 127, 199, 111, 62, 135, 248,
    174, 169, 211, 58, 66, 154, 106, 195, 245, 171, 17, 187, 182, 179, 0, 243,
    132, 56, 148, 75, 128, 133, 158, 100, 130, 126, 91, 13, 153, 246, 216, 219,
    119, 68, 223, 78, 83, 88, 201, 99, 122, 11, 92, 32, 136, 114, 52, 10,
    138, 30, 48, 183, 156, 35, 61, 26, 143, 74, 251, 94, 129, 162, 63, 152,
    170, 7, 115, 167, 241, 206, 3, 150, 55, 59, 151, 220, 90, 53, 23, 131,
    125, 173, 15, 238, 79, 95, 89, 16, 105, 137, 225, 224, 217, 160, 37, 123,
    118, 73, 2, 157, 46, 116, 9, 145, 134, 228, 207, 212, 202, 215, 69, 229,
    27, 188, 67, 124, 168, 252, 42, 4, 29, 108, 21, 247, 19, 205, 39, 203,
    233, 40, 186, 147, 198, 192, 155, 33, 164, 191, 98, 204, 165, 180, 117, 76,
    140, 36, 210, 172, 41, 54, 159, 8, 185, 232, 113, 196, 231, 47, 146, 120,
    51, 65, 28, 144, 254, 221, 93, 189, 194, 139, 112, 43, 71, 109, 184, 209]


-- buf :: IO (MVector (M.PrimState IO) Int16)
-- buf = M.replicate 240 0

log_1_5 :: Float
log_1_5 = 0.4054651
log_1_3 :: Float
log_1_3 = 0.26236426
log_1_1 :: Float
log_1_1 = 0.095310180

-- tlshText :: TL.Text -> Hash
-- tlshText t = Hash "2345"

bMapping :: Word8 -> Char -> Char -> Char -> Int
bMapping salt i j k = fromEnum h4
  where
    h4 = go h3 (o k)
    h3 = go h2 (o j)
    h2 = go h1 (o i)
    h1 = go h0 salt
    h0 = 0
    o = toEnum . ord
    go a b = vTable ! (fromEnum $ xor a b)

lCapturing :: Int -> Int
lCapturing len
  | len <= 656 = fun len log_1_5 0.0
  | len <= 3199 = fun len log_1_3 8.72777
  | otherwise = fun len log_1_1 62.5472
  where
    fun :: Int -> Float -> Float -> Int
    fun len logc sub = toEnum . floorFloatInt $
      (log . fromIntegral $ len) / logc - sub

swapByte :: Word8 -> Word8
swapByte i = a .|. b
  where
    a = (shiftR (i .&. 0xf0) 4) .&. 0x0f
    b = (shiftL (i .&. 0x0f) 4) .&. 0xf0

type V_16 = Vector Int16

arraySize :: Int
arraySize = 256

-- TODO repa package to see

bitPairsDiffTable :: Vector (Vector Int16)
bitPairsDiffTable = generate arraySize row
  where
    row i = generate arraySize (col i)
    col :: Int -> Int -> Int16
    col i j =
      let x = i
          y = j
          d = 0
          diff =0
      in
        let a1 = stp (i, j, 0, 0)
        in let a2 = stp a1
           in let a3 = stp a2
              in let (_,_,_,diff) = stp a3
                 in toEnum diff
    stp :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
    stp (x, y, d, diff) =
      let d = abs (x `mod` 4 - y `mod` 4)
          diff = diff + if d == 3 then 6 else d
          x = shiftR x 2
          y = shiftR y 2
      in (x, y, d, diff)


hDistance :: Bucket ->
             Bucket ->
             Int16
hDistance x y = do s
  where
    s = L.foldr sumGo 0 (zipGo x y)
    sumGo :: (Word8, Word8) -> Int16 -> Int16
    sumGo (a, b) agg = agg + (bitPairsDiffTable ! (o b)) ! (o a)
    o :: Word8 -> Int
    o = fromEnum
    zipGo _ _ = [(1,1)]

sliding_wnd_size :: Int
sliding_wnd_size = 5
rng_size :: Int
rng_size = sliding_wnd_size
rng_idx :: Int -> Int
rng_idx i = (i+rng_size) `mod` rng_size
tlsh_checksum_len :: Int
tlsh_checksum_len = 1
buckets :: Int
buckets = 256
eff_buckets :: Int
eff_buckets = 128
code_size :: Int
code_size = 32   -- 128 * 2 bits = 32 bytes
tlsh_string_len :: Int64
tlsh_string_len = 70  -- 2 + 1 + 32 bytes = 70 hexidecimal chars
range_lvalue :: Word8
range_lvalue = 256
range_qratio :: Word8
range_qratio = 16
int_digest_length = shiftR buckets 2
int_digest_header = 3
digest_length = (shiftR buckets 1) + 3

{-
getQLo :: (Bits a, Num a) => a -> a
getQLo q = q .&. 0x0f
getQHi :: (Bits a, Num a) => a -> a
getQHi q = shiftR (q .&. 0xf0) 4

setQLo :: (Bits a, Num a) => a -> a -> a
setQLo q x = (q .&. 0xf0) .|. (x .&. 0x0f)
setQHi :: (Bits a, Num a) => a -> a -> a
setQHi q x = (q .&. 0x0f) .|. ( shiftL (x .&. 0x0f) 4)

modDiff :: IO (M.MVector (M.PrimState IO) Word8) ->
           IO (M.MVector (M.PrimState IO) Word8) -> Word8 -> IO Word8
modDiff vmx vmy r = do
  mx <- vmx
  my <- vmy
  x <- M.read mx 0
  y <- M.read my 0
  let (dl, dr) = if x > y then (y-x, x+r-y) else (x-y, y+r-x)
  if dl>dr then return dr else return dl


totalDiff :: TLSH -> TLSH -> Bool -> Int
totalDiff this other lenDiff =
  if this == other then 0
  else let diff = 0
       in let diff = if lenDiff then
                       let ldiff = modDiff (lValue this) (lValue other) range_lvalue
                       in if ldiff == 0 then 0 else if ldiff == 1 then 1 else diff + ldiff*12
                     else 0
          in let q1diff = modDiff (getQLo . q $ this) (getQLo . q $ other) range_qratio
             in let diff = diff + if q1diff <= 1 then q1diff else (q1diff - 1)*12
                in let q2diff = modDiff (getQHi . q $ this) (getQHi . q $ other) range_qratio
                   in let diff = diff + if q2diff <= 1 then q2diff else (q2diff - 1)*12
                      in let diff = diff + microHamming (checksum this) (checksum other)
                         in let diff = diff + hDist (tmpCode this) (tmpCode other)
                            in toEnum $ maybe 0 id diff
  where
    hDist :: IO (M.MVector (M.PrimState IO) Word8) ->
             IO (M.MVector (M.PrimState IO) Word8) ->
             Maybe Int
    hDist ma mb = do
      a <- liftIO $ ma
      b <- liftIO $ mb
      return . fromEnum $ hDistance a b

    microHamming ch1 ch 2 = 1 -- TODO

fromHex :: Text -> Vector Int16
fromHex text = fromList $ Prelude.Compat.map goHd (TL.unpack text)
  where
    goHd = toEnum . hexDigitToInt

fromTlshStr :: TL.Text -> Either String (Vector Int16)
fromTlshStr text = if TL.length text /= tlsh_string_len then Left "string has wrong length"
                   else Right . fromHex $ text
                        -- return TLSH with fields
-}
