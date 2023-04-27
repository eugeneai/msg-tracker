{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}

module TLSH
  (
    tlshText
  )
  where

import Prelude.Compat
import Data.Bits ( Bits(..) )
import qualified Data.Vector.Unboxed.Mutable as M
import Data.Vector.Unboxed
import Data.Text.Lazy as TL
import Data.Int (Int8, Int16, Int32, Int64)
import qualified Data.ByteArray as BA
import GHC.Integer (xorInteger)
import Data.Word8 (Word8)
import qualified GHC.Types as G
import GHC.Float.RealFracMethods (floorFloatInt)
import Data.Text.Internal.Read (hexDigitToInt)
-- import Data.Hex

v_table :: Vector Word8
v_table = fromList [
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

newtype Hash = Hash String

tlshText :: TL.Text -> Hash
tlshText t = Hash "2345"

b_mapping :: Word8 -> Word8 -> Word8 -> Word8 -> Word8
b_mapping salt i j k = h4
  where
    h4 = v_table ! xor h3 k
    h3 = v_table ! xor h2 j
    h2 = v_table ! xor h1 i
    h1 = v_table ! xor h0 salt
    h0 = 0
    -- h4 = BA.index v_table $ xor h3 k
    -- h3 = BA.index v_table $ xor h2 j
    -- h2 = BA.index v_table $ xor h1 i
    -- h1 = BA.index v_table $ xor h0 salt
    -- h0 = 0


l_capturing :: Float -> Int16
l_capturing len = (q len) .&. (255::Int16)
  where
    q len
      | len <= 656 = floorFloatInt (log len / log_1_5)
      | len <= 3199 = floorFloatInt (log len / log_1_3 - 8.72777)
      | otherwise = floorFloatInt (log len / log_1_1 - 62.5472)

swap_byte :: Int16 -> Int16
swap_byte i = a .|. b
  where
    a = (shiftR (i .&. 0xf0) 4) .&. 0x0f
    b = (shiftL (i .&. 0x0f) 4) .&. 0xf0

-- toHex
-- fromHex

modDiff x y r = if dl>dr then dr else dl
  where
    (dl, dr) = if x > y then (y-x, x+r-y) else (x-y, y+r-x)

arraySize = 256
bitPairsDiffTable :: Vector (Vector Int16)
bitPairsDiffTable = generate arraySize row
  where
    row i = generate arraySize (col i)
    col i j =
      let x = i
          y = j
          d = 0
          diff =0
      in
        let a1 = stp (i, j, 0, 0)
        in let a2 = stp a1
           in let a3 = stp a2
              in let (_,_,_,diff) = stp a23
                 in diff
    stp (x, y, d, diff) =
      let d = abs (x `mod` 4 - y `mod` 4)
          diff = diff + if d == 3 then 6 else d
          x = floorFloatInt (x/4)
          y = floorFloatInt (y/4)
      in (x, y, d, diff)


hDistance x y = s
  where
    s = TL.foldr sum 0 $ TL.zip x y
    sum (a,b) acc = acc + (bitPairsDiffTable ! b) ! a

sliding_wnd_size = 5
rng_size = sliding_wnd_size
rng_idx i = i+rng_size `mod` rng_size
tlsh_checksum_len = 1
buckets = 256
eff_buckets = 128
code_size = 32   -- 128 * 2 bits = 32 bytes
tlsh_string_len = 70  -- 2 + 1 + 32 bytes = 70 hexidecimal chars
range_lvalue = 256
range_qratio = 16

swapUnit buf x y = do
  M.swap buf x y

partition buf lfet right = do
  if left == right then do return left
    else if (left+1) == right then do
      swapUnit buf left rigth
      return left
    else do
      let ret = left
          pivot = shiftR (left + right) 1
          val = M.read buf pivot

      nret <- permuteGo val left rigth ret left
      nretval <- M.read buf nret
      M.write buf right nretval
      M.write buf nret val
  where
    permuteGo val l r ret i
      | i < r = do
          iv <- M.read buf i
          if iv<val then do
            swapUnit buf ret i
            return $ permuteGo val l r (ret+1) (i+1)
          else do
            return $ permuteGo val l r ret (i+1)
      | otherwise = do
            return ret

-- findQuartile tlsh quartiles =



data TLSH = TLSH { checksum :: IO (MVector (M.PrimState IO) Int16)
                 , slideWindow :: IO (MVector (M.PrimState IO) Int16)
                 , aBucket :: IO (MVector (M.PrimState IO) Int32)
                 , dataLen :: IO (MVector (M.PrimState IO) Int16)
                 , lValue :: IO (MVector (M.PrimState IO) Int16)
                 , q :: IO (MVector (M.PrimState IO) Int16)
                 , lshCodeValid :: IO (MVector (M.PrimState IO) Bool)
                 , tmpCode :: IO (MVector (M.PrimState IO) Word8)
                 , lshCode :: IO (MVector (M.PrimState IO) Word8)}


emptyTlsh :: TLSH
emptyTlsh = TLSH { checksum = M.replicate tlsh_checksum_length 0
                 , slideWindow = M.replicate slidingWndSize 0
                 , aBucket = M.replicate buckets 0
                 , dataLen = M.replicate 1 0
                 , tmpCode = M.replicate code_size 0
                 , lValue = M.replicate 1 0
                 , q = M.replicate 1 0
                 , lshCode = ""
                 , lshCodeValid = M.replicate 1 False}


hash :: TLSH -> Either String TLSH
hash tlsh = do
  if not . lshCodeValid $ tlsh then do
    return $ Left "ERROR IN PROCESSING"
  else do
    let tmp = emptyTlsh
    swapBytes (checksum tmp)
    swapByte (lValue tmp)
  where
    swapBytes chksum = do
      return chksum



getQLo q = q .&. 0x0f
getQHi q = shiftR (q .&. 0xf0) 4

setQLo q x = (q .&. 0xf0) .|. (x .&. 0x0f)
setQHi q x = (q .&. 0x0f) .|. ( shiftL (x .&. 0x0f) 4)

totalDiff :: TLSH -> TLSH -> Int32
totalDiff this other lenDiff =
  if this == other then 0
  else let diff = 0
       in let diff = if lenDiff then
                       let ldiff = modDiff (lValue this) (lValue other) range_lvalue
                       in if ldiff == 0 then 0 else if ldiff == 1 then 1 else diff + ldiff*12
                     else 0
          in let q1diff = modDiff (getQLo . q $ this) (getQlo . q $ other) range_qratio
             in let diff = diff + if q1diff <= 1 then q1diff else (q1diff - 1)*12
                in let q2diff = modDiff (getQHi . q $ this) (getQHi . q $ other) range_qratio
                   in let diff = diff + if q2diff <= 1 then q2diff else (q2diff - 1)*12
                      in let diff = diff + microHamming (checksum this) (checksum other)
                         in let diff = diff + hDistance code_size (tmpCode this) (tmpCode other)
                            in diff
  where
    microHamming ch1 ch 2 = 1 -- TODO

fromHex text = Prelude.Compat.map hexDigitToInt (TL.unpack text)

fromTlshStr :: TL.Text -> Vector Int32
fromTlshStr text = if TL.length text /= tlsh_string_len then Left "string has wrong length"
                   else Right . fromHex $ text
                        -- return TLSH with fields
