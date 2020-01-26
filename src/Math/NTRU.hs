{- |  
Module      : NTRU
Description : NTRU cryptographic system implementation
Maintainer  : julrich@cyberpointllc.com
Stability   : Experimental
License     : GPL

This is an implementation of the NTRU cryptographic system, following the standard set forth 
by the IEEE in the document entitled IEEE Standard Specification for Public Key Cryptographic 
Techniques Based on Hard Problems over Lattices (IEEE Std 1363.1-2008). It is designed to be compatible with the implementation
of SecurityInnovations, available <https://www.securityinnovation.com/products/encryption-libraries/ntru-crypto/ here>. 
-}



module Math.NTRU (keyGen, encrypt, decrypt, genParams, ParamSet(..)) where

import Data.Digest.Pure.SHA
import Data.List.Split
import Data.Sequence as Seq (index, update, fromList, Seq)
import Data.Foldable as L (toList)
import Crypto.Random
import System.Random
import Math.Polynomial
import Math.NumberTheory.Moduli 
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as BL


{- Polynomial Operations -} 

-- | Poly to List
fromPoly :: Poly Integer -> [Integer]
fromPoly = polyCoeffs LE 

-- | List to Poly
toPoly :: [Integer] -> Poly Integer  
toPoly = poly LE 

-- | Retrive the coefficient of p corresponding to the (x^i) term 
polyCoef :: Poly Integer -> Int -> Integer
polyCoef p i = fromPoly p !! i 

-- | Useful for syntax. Allows for poly + poly or poly * poly. 
-- | Note that for ring multiplication, reduceDegree must be called
instance (Num a, Eq a) => Num (Poly a) where
  f + g = addPoly f g
  f * g = multPoly f g
  negate = negatePoly
  abs = undefined
  signum = undefined
  fromInteger = undefined

-- | Allows for polynomial multipliction in the ring of size n: reduceDegree n (a * b) = a * b in the ring. Assumes: (degree f) <= 2n
reduceDegree :: Int -> Poly Integer -> Poly Integer 
reduceDegree n f =
  let (f1,f2) = splitAt n (fromPoly f) 
  in toPoly f1 + toPoly f2 

-- | Reduces all of the polynomial's coefficents mod q
polyMod :: Integer -> Poly Integer -> Poly Integer
polyMod q f = toPoly $ map (`mod` q) (fromPoly f)

-- | Same as polyMod, but chooses representative group values in Z/nZ to be in (-q/2, q/2] instead of [0,q-1]
polyModInterval :: Integer -> Poly Integer -> Poly Integer
polyModInterval q f = toPoly $ map (\x' -> intervalReduce $ x' `mod` q) (fromPoly f)  
  where intervalReduce x' = if x' <= (q `div` 2) then x' else x' - q

-- | PolyMod when q is big 
polyBigMod :: Integer -> Poly Integer -> Poly Integer
polyBigMod q p = toPoly $ map fromIntegral $ fromPoly $ polyMod q $ toPoly $ map fromIntegral $ fromPoly p 

-- | Creates the polynomial x^n
xPow :: Int -> Poly Integer 
xPow = powPoly x


{- Key Generation -}

-- | 6.3.3.1 Divides one polynomial by another mod p: let (q,r) = divPolyMod p a b; ((b * q) + r) `mod` p = a; (degree r) < (degree b)
divPolyMod :: Integer -> Poly Integer -> Poly Integer -> (Poly Integer, Poly Integer)
divPolyMod p a b = 
  let n = polyDegree b in 
  let u = inverseMod (polyCoef b n) p in 
  divLoop p b n u zero a
  where 
    divLoop p' b' n' u' q r =
      let d = polyDegree r in 
      if d < n' then (polyMod p' q, polyMod p r)
      else
        let v = scalePoly (u' * polyCoef r d) (xPow (d - n')) in 
        let r' = polyMod p' $ r - (v * b') in 
        let q' = polyMod p' $ q + v in 
      divLoop p' b' n' u' q' r'

-- | 6.3.3.2 Finds the extended GCD mod p: let (d,u) = extendedEuclidean p a b; if d == 1, then (u * a) `mod` p = 1 
extendedEuclidean :: Integer -> Poly Integer -> Poly Integer -> (Poly Integer, Poly Integer)
extendedEuclidean p a b = extendedEuclideanLoop p one a zero b
  where 
    extendedEuclideanLoop p' u d v1 v3
      | polyIsZero v3 = (d,u)
      | otherwise = 
        let (q,t3) = divPolyMod p' d v3 in 
        let t1 = polyMod p' $ u - q * v1 in 
        extendedEuclideanLoop p' v1 v3 t1 t3 

-- | Generates Polynomials and Attempts to Find Inverses Until Success: let (a,u) = findInvertible params; (a * u) `mod` 2 = 1  
findInvertible :: ParamSet -> IO (Poly Integer, Poly Integer)
findInvertible params = do 
    let n =  getN params 
    let df = getDf params 
    a' <- genRandPoly n df df  
    let a = scalePoly (getP params) a' + one
    let b = xPow n - one
    let (d, u) = extendedEuclidean 2 a b 
    if d == one then return (a, u) else findInvertible params  

-- | 6.3.3.4 Raises Polynomial Inverse mod 2 to mod 2^11; let (a, b) = findInvertible; (a * (inverseLift a b (degree a))) `mod` 2048 = 1 
inverseLift :: Poly Integer -> Poly Integer -> Int -> Integer -> Poly Integer
inverseLift a b deg = inverseLift' a b deg (2 :: Integer) (11 :: Integer) where 
  inverseLift' a b deg n e q 
    | e == 0 = polyMod (2 ^ q) b
    | otherwise = 
        let b' = polyBigMod (2 ^ n) $ scalePoly 2 b - (reduceDegree deg $! a * (reduceDegree deg $! (b * b))) 
        in inverseLift' a b' deg (2 * n) (e `div` 2) q 

-- | Generates a random PublicKey-PrivateKey Pair 
keyGen :: ParamSet -- ^ Parameter set, most likely the output of 'genParams'
          -> IO ([Integer], [Integer]) -- ^ A tuple representing (PublicKey, PrivateKey) where PrivateKey = 1 + pf, per <https://www.securityinnovation.com/uploads/Crypto/NTRU%20Enhancements%201.pdf enhancement #2>.
keyGen params = do 
  let n =  getN params 
      dg = getDg params
      q = getQ params  
  (f, u) <- findInvertible params 
  let fq = inverseLift f u n (fromIntegral q) 
  g <- genRandPoly n dg (dg - 1) 
  let pk = polyMod q $! reduceDegree n $! scalePoly (getP params) $! fq * g
  return (fromPoly pk, fromPoly f)


{- Blinding Polynomial Generation -}

-- | Creates seed for bpgm. h is the public key, b is the random string of bits prefixed to the message
genSData :: [Integer] -> [Integer] -> [Integer] -> ParamSet -> [Integer]
genSData h msg b params = 
  let bh = concatMap bigIntToBits h in 
  let pkLen = getPkLen params in 
  let bhTrunc = take (pkLen - (pkLen `mod` 8)) bh in 
  let hTrunc = map (fromIntegral . bitsToInt) (chunksOf 8 bhTrunc) in 
  let sData = map fromIntegral (getOID params) ++ msg ++ b ++ hTrunc in 
  sData

-- | 8.3.2.2 Generates the blinding polynomial using the given seed
bpgm :: [Integer] -> ParamSet -> [Integer]
bpgm seed params =
  let (i, s) = igf ([], [], 0) seed params in
  let r = Seq.update i 1 $ Seq.fromList $ replicate (getN params) 0 in
  let t = getDr params in
  let r' = rlooper s 1 r (t - 1) params in
  L.toList $ rlooper s (-1) r' t params

-- | Creates the sequence with the proper -1's and 1's
rlooper :: ([Integer], [Integer], Integer) -> Integer -> Seq.Seq Integer -> Int -> ParamSet -> Seq.Seq Integer
rlooper s val r 0 params = r
rlooper s val r t params =
  let (i, s') = igf s [] params in
  if Seq.index r i == 0
    then (let r' = Seq.update i val r in rlooper s' val r' (t-1) params)
    else rlooper s' val r t params

-- | 8.4.2.1 Given a state or a seed, generates the next index to be used
igf :: ([Integer], [Integer], Integer) -> [Integer] -> ParamSet -> (Int, ([Integer], [Integer], Integer))
igf state seed params =
  let (z, buf, counter) = extractVariables state seed params 
      (i, buf', counter') = genIndex counter buf z params
      s = (z, buf', counter')
      n =  getN params 
  in (i `mod` n, s)

-- | Either initializes the state, or uses the already created one 
extractVariables :: ([Integer], [Integer], Integer) -> [Integer] -> ParamSet -> ([Integer], [Integer], Integer) 
extractVariables state [] _ = state
extractVariables _ seed params = igfinit seed params 

-- | Initialization of state
igfinit :: [Integer] -> ParamSet -> ([Integer], [Integer], Integer)
igfinit seed params = 
  let minCallsR = getMinCallsR params  
      shaFn =  getSHA params 
      z = shaFn seed  
      buf = buildM 0 minCallsR z shaFn []
  in (z, buf, minCallsR)

-- | Returns an index and pieces of the state
genIndex :: Integer -> [Integer] -> [Integer] -> ParamSet -> (Int, [Integer], Integer)
genIndex counter buf z params =
  let remLen =  length buf
      c = getC params 
      n =  getN params 
      shaFn =  getSHA params
      hLen =  getHLen params  
      tmpLen =  (c - remLen)
      cThreshold = counter + fromIntegral (ceiling (fromIntegral tmpLen / fromIntegral hLen))
      (m, counter') = if remLen >= c 
                      then (buf, counter)
                      else (buildM counter cThreshold z shaFn buf, cThreshold)
      (b, buf') = splitAt c (buf ++ m)
      i = fromIntegral $ bitsToInt b 
  in if i >= (2^c - (2^c `mod` n))
     then genIndex counter' buf' z params 
     else (i, buf', counter')

-- | Builds out the buffer 
buildM :: Integer -> Integer -> [Integer] -> ([Integer]->[Integer]) -> [Integer] -> [Integer]
buildM count cThreshold z shaFn buf
  | count >= cThreshold = buf 
  | otherwise = 
    let c = i2osp count 3 
        h =  shaFn (z ++ c) 
        m = buf ++ intsToBits h
    in buildM (count + 1) cThreshold z shaFn m 

-- | Converts counter to 4 bytes... Not exactly the same as documentation but in practice counter does not exceed the bounds
i2osp :: Integer -> Integer -> [Integer]
i2osp i n 
  | n == 0 = [i] 
  | otherwise = 0:i2osp i (n-1)


{- SHA Functionality -}

-- | Needed to pass sha() output to unpack()
bToStrict :: BL.ByteString -> B.ByteString
bToStrict = B.concat . BL.toChunks

-- | sha1 output: 20 octets (1 octet = 8 bits)
sha1Octets :: [Integer] -> [Integer]
sha1Octets input = map fromIntegral $ B.unpack $ bToStrict $ bytestringDigest $ sha1 $ BL.pack $ map fromIntegral input

-- | sha256 output: 32 octets
sha256Octets :: [Integer] -> [Integer]
sha256Octets input = map fromIntegral $ B.unpack $ bToStrict $ bytestringDigest $ sha256 $ BL.pack $ map fromIntegral input


{- Mask Generation -} -- Much of this code is similar to blinding polynomial generation, but we implemented separately 

-- | 8.4.1.1 Generates the mask based on the given seed 
mgf :: [Integer] -> ParamSet -> [Integer]
mgf seed params =
  let n =  getN params in
  let shaFn =  getSHA params in 
  let z = shaFn seed in 
  let buf = buildBuffer 0 (getMinCallsR params) z shaFn [] in 
  let i = formatI buf in
  take n $ finishI i n (getMinCallsR params) z shaFn

-- | Builds out the buffer 
buildBuffer :: Integer -> Integer -> [Integer] -> ([Integer]->[Integer]) -> [Integer] -> [Integer]
buildBuffer counter minCallsR z shaFn buffer
  | counter >= minCallsR = buffer
  | otherwise = let octet_c = i2osp counter 3 in  
                let h = shaFn (z ++ octet_c) in 
                buildBuffer (counter + 1) minCallsR z shaFn (buffer ++ h)

-- | Step I Converts octets to trits
toTrits :: Integer -> Integer -> [Integer]
toTrits n o
  | n == 0 = []
  | otherwise = (o `mod` 3):toTrits (n - 1) ((o - (o `mod` 3)) `div` 3)

-- | Builds out buffer when needed
finishI :: [Integer] -> Int -> Integer -> [Integer] -> ([Integer] -> [Integer]) -> [Integer]
finishI i n counter z shaFn
  | fromIntegral (length i) >= n = i 
  | otherwise = let buf = buildBuffer counter (counter + 1) z shaFn [] in 
                let i' = formatI buf in 
                finishI i' n (counter + 1) z shaFn 

-- | Formats buffer
formatI :: [Integer] -> [Integer]
formatI buf = concatMap (toTrits 5) $ filter (< 243) buf

{- Encrypt -}

-- | Encrypts a message using the given parameter set
encrypt :: ParamSet -- ^ Parameter set, most likely the output of 'genParams' 
           -> [Integer] -- ^ A list of ASCII values representing the message
           -> [Integer] -- ^ A list of numbers representing the public key
           -> IO [Integer] -- ^ A list of numbers representing the ciphertext
encrypt params msg h =  
  let l = fromIntegral $ length msg
      maxLength = getMaxMsgLenBytes params in
  if l > maxLength then error "message too long"
  else do 
    let bLen =  getDb params `div` 8 
        dr = getDr params 
        n =  getN params
        q = getQ params
        p = getP params 
    b <- randByteString bLen
    let p0 = replicate (fromIntegral $ maxLength - l) 0
        m = b ++ [fromIntegral l] ++ msg ++ p0 
        mBin =  addPadding $ intsToBits m 
        mTrin =  concatMap binToTern $ chunksOf 3 mBin
        sData = genSData h msg b params
        r = bpgm sData params
        r' = polyMod q $ reduceDegree n $ toPoly r * toPoly h
        r4 = polyMod 4 r'
        or4 = toOctets $ fromPoly r4
        mask = mgf or4 params 
        m' = polyModInterval p $ toPoly mask + toPoly mTrin
        e = polyMod q $ r' + m' 
    return $ fromPoly e


{- Decrypt -}

-- | 9.3.3 Decrypts e using the private key f and verifies it using the public key h. 
decrypt :: ParamSet -- ^ Parameter set, most likely the output of 'genParams' 
           -> [Integer] -- ^ A list of numbers representing the private key
           -> [Integer] -- ^ A list of numbers representing the public key
           -> [Integer] -- ^ A list of numbers representing the ciphertext
           -> Maybe [Integer] -- ^ A list of numbers representing the original message
decrypt params f h e =
  let n =  getN params
      p = getP params
      q = getQ params 
      bLen =  getDb params `div` 8
      ci = polyMod p $ polyModInterval q $ reduceDegree n $ toPoly f * toPoly e
      cR = polyMod q $ toPoly e - polyModInterval p ci
      cR4 = polyMod 4 cR
      coR4 = toOctets $ fromPoly cR4
      cMask = polyMod p $ toPoly $ mgf coR4 params
      cMTrin =  polyModInterval p $ ci - cMask 
      cMTrin' = improperPolynomial n $ fromPoly cMTrin
      cMBin =  concatMap ternToBin $ chunksOf 2 $ take (length cMTrin' - (length cMTrin' `mod` 2)) cMTrin'
      cM = map bitsToInt $ chunksOf 8 $ take (length cMBin - (length cMBin `mod` 8)) cMBin
      (cb, rest) = splitAt bLen cM
      ([cl], rest') = splitAt (getLLen params) rest
      (cm, rest'') = splitAt (fromIntegral cl) rest'
      sData = genSData h cm cb params 
      cr = bpgm sData params
      cR' = polyMod q $ reduceDegree n $ toPoly cr * toPoly h
      validR = cR' == cR
      validRemainder = all (==0) rest''
  in checkValid cm validR validRemainder 

-- | Checks results of verification steps
checkValid :: [Integer] -> Bool -> Bool -> Maybe [Integer]
checkValid _ _ False = Nothing
checkValid _ False _ = Nothing
checkValid m _ _ = Just m 


{- Other Operations -}

-- | Calculate the modular inverse of x and y: ((inverseMod x y) * x) `mod` y = 1 
inverseMod :: Integer -> Integer -> Integer
inverseMod x y = case invertMod (fromIntegral x) (fromIntegral y) of
  Just n -> fromIntegral n 
  _ -> error "Could not calculate inverseMod"

-- | Generate a random ByteString
randByteString :: Int -> IO [Integer]
randByteString size = do
  g <- newGenIO :: IO SystemRandom
  case genBytes size g of 
    Left err -> error $ show err
    Right (result, g2) -> return (unpackByteString result)

-- | Converts a bytestring to a list of ascii values 
unpackByteString :: BC.ByteString -> [Integer]
unpackByteString str = map fromIntegral (B.unpack str) 

-- | Used to encode bits of a message from binary to trinary representation 
binToTern :: [Integer] -> [Integer]
binToTern [0,0,0] = [0,0]
binToTern [0,0,1] = [0,1]
binToTern [0,1,0] = [0,-1]
binToTern [0,1,1] = [1,0]
binToTern [1,0,0] = [1,1]
binToTern [1,0,1] = [1,-1]
binToTern [1,1,0] = [-1,0]
binToTern [1,1,1] = [-1,1]
binToTern _ = error "Problem converting binary to trinary"

-- | Inverse of binToTern
ternToBin :: [Integer] -> [Integer]
ternToBin [0,0] = [0,0,0]
ternToBin [0,1] = [0,0,1]
ternToBin [0,-1] = [0,1,0]
ternToBin [1,0] = [0,1,1]
ternToBin [1,1] = [1,0,0]
ternToBin [1,-1] = [1,0,1]
ternToBin [-1,0] = [1,1,0]
ternToBin [-1,1] = [1,1,1]
ternToBin _ = error " Problem converting trinary to binary"


-- | Makes message length a multiple of 3 by padding with 0s
addPadding :: [Integer] -> [Integer]
addPadding m = case length m `mod` 3 of
  0 -> m
  1 -> m ++ [0,0]
  2 -> m ++ [0]


-- | Converts a single byte to a list of (n+1) bits: unpackByte 7 3 = [0,0,0,0,0,0,1,1]
unpackByte :: Integer -> Integer -> [Integer]
unpackByte n b 
  | n < 0 = []
  | otherwise = (b `div` (2 ^ n)):unpackByte (n-1) (b `mod` 2 ^ n)

-- | Converts a byte to a list of 8 bits
intToBits :: Integer -> [Integer]
intToBits = unpackByte 7

-- | Converts a byte to a list of 11 bits. Needed for blinding polynomial seed 
bigIntToBits :: Integer -> [Integer]
bigIntToBits = unpackByte 10

-- | Turns a list of integers into bits 
intsToBits :: [Integer] -> [Integer]
intsToBits = concatMap intToBits

-- | Converts a list of bits to a single byte: bitsToInt [0,0,0,0,0,0,1,1] = 3  
bitsToInt :: [Integer] -> Integer
bitsToInt b = packByte 1 (reverse b) 
  where
    packByte n b
      | null b = 0
      | otherwise = n * head b + packByte (n * 2) (tail b)

-- | Generates a random polynomial of degree < n with pos 1's and neg -1's. Assumes pos + neg <= n
genRandPoly :: Int -> Int -> Int -> IO (Poly Integer)
genRandPoly n pos neg = do 
  poly <- setRandValues [] n pos neg
  return $ toPoly poly  
  where
    setRandValues lst n pos neg = 
      if n == 0 then return lst 
      else do
        randVal <- randomIO :: IO Int
        let randInRange = randVal `mod` n 
        if randInRange < pos 
          then setRandValues ((1):lst) (n - 1) (pos - 1) neg else if randInRange < (pos + neg) then setRandValues ((-1):lst) (n - 1) pos (neg - 1) else setRandValues (0:lst) (n - 1) pos neg

-- | Creates an improper polynomial of length n from poly
improperPolynomial :: Int -> [Integer] -> [Integer]
improperPolynomial n poly = poly ++ replicate (fromIntegral n - length poly) 0

-- | Pads the given list with the requisite zeros to have a multiple of 8 length 
padInt8 :: [Integer] -> [Integer]
padInt8 lst = lst ++ replicate ((8 - (length lst `mod` 8)) `mod` 8) 0 

-- | Converts to octets
toOctets :: [Integer] -> [Integer]
toOctets lst = 
  let int2s = concatMap (reverse . take 2 . reverse . unpackByte 7) lst 
  in map (bitsToInt . padInt8) $ chunksOf 8 int2s


{- Paramter Sets -}

-- | Generates the proper parameter set based on the given bit level
genParams :: String -- ^ Desired parameter set: This should be either one of the 12 listed in the IEEE Standard (1363.1-2008) Annex A
             -> ParamSet -- ^ Parameter set to be used by 'keyGen', 'encrypt', or 'decrypt'
genParams bit_level 
  | bit_level == "EES401EP1" = ParamSet {getN =  401, getP = 3, getQ = 2048, getDf = 113, getDg = 133, getLLen = 1, getDb = 112, getMaxMsgLenBytes = 60, getBufferLenBits = 600, getBufferLenTrits = 400, getDm0 = 113, getShaLvl = 1, getDr = 113, getC = 11, getMinCallsR = 32, getMinCallsMask = 9, getOID = [0,2,4], getPkLen = 114, getBitLvl = 112} 
  | bit_level == "EES449EP1" = ParamSet {getN =  449, getP = 3, getQ = 2048, getDf = 134, getDg = 149, getLLen = 1, getDb = 128, getMaxMsgLenBytes = 67, getBufferLenBits = 672, getBufferLenTrits = 448, getDm0 = 134, getShaLvl = 1, getDr = 134, getC = 9, getMinCallsR = 31, getMinCallsMask = 9, getOID = [0,3,3], getPkLen = 128, getBitLvl = 128} 
  | bit_level == "EES677EP1" = ParamSet {getN =  677, getP = 3, getQ = 2048, getDf = 157, getDg = 225, getLLen = 1, getDb = 192, getMaxMsgLenBytes = 101, getBufferLenBits = 1008, getBufferLenTrits = 676, getDm0 = 157, getShaLvl = 256, getDr = 157, getC = 11, getMinCallsR = 27, getMinCallsMask = 9, getOID = [0,5,3], getPkLen = 192, getBitLvl = 192} 
  | bit_level == "EES1087EP2" = ParamSet {getN =  1087, getP = 3, getQ = 2048, getDf = 120, getDg = 362, getLLen = 1, getDb = 256, getMaxMsgLenBytes = 170, getBufferLenBits = 1624, getBufferLenTrits = 1086, getDm0 = 120, getShaLvl = 256, getDr = 120, getC = 13, getMinCallsR = 25, getMinCallsMask = 14, getOID = [0,6,3], getPkLen = 256, getBitLvl = 256} 
  | bit_level == "EES541EP1" = ParamSet {getN =  541, getP = 3, getQ = 2048, getDf = 49, getDg = 180, getLLen = 1, getDb = 112, getMaxMsgLenBytes = 86, getBufferLenBits = 808, getBufferLenTrits = 540, getDm0 = 49, getShaLvl = 1, getDr = 49, getC = 12, getMinCallsR = 15, getMinCallsMask = 11, getOID = [0,2,5], getPkLen = 112, getBitLvl = 112} 
  | bit_level == "EES613EP1" = ParamSet {getN =  613, getP = 3, getQ = 2048, getDf = 55, getDg = 204, getLLen = 1, getDb = 128, getMaxMsgLenBytes = 97, getBufferLenBits = 912, getBufferLenTrits = 612, getDm0 = 55, getShaLvl = 1, getDr = 55, getC = 11, getMinCallsR = 16, getMinCallsMask = 13, getOID = [0,3,4], getPkLen = 128, getBitLvl = 128} 
  | bit_level == "EES887EP1" = ParamSet {getN =  887, getP = 3, getQ = 2048, getDf = 81, getDg = 295, getLLen = 1, getDb = 192, getMaxMsgLenBytes = 141, getBufferLenBits = 1328, getBufferLenTrits = 886, getDm0 = 81, getShaLvl = 256, getDr = 81, getC = 10, getMinCallsR = 13, getMinCallsMask = 12, getOID = [0,5,4], getPkLen = 192, getBitLvl = 192} 
  | bit_level == "EES1171EP1" = ParamSet {getN =  1171, getP = 3, getQ = 2048, getDf = 106, getDg = 390, getLLen = 1, getDb = 256, getMaxMsgLenBytes = 186, getBufferLenBits = 1752, getBufferLenTrits = 1170, getDm0 = 106, getShaLvl = 256, getDr = 106, getC = 10, getMinCallsR = 20, getMinCallsMask = 15, getOID = [0,6,4], getPkLen = 256, getBitLvl = 256} 
  | bit_level == "EES659EP1" = ParamSet {getN =  659, getP = 3, getQ = 2048, getDf = 38, getDg = 219, getLLen = 1, getDb = 112, getMaxMsgLenBytes = 108, getBufferLenBits = 984, getBufferLenTrits = 658, getDm0 = 38, getShaLvl = 1, getDr = 38, getC = 11, getMinCallsR = 11, getMinCallsMask = 14, getOID = [0,2,6], getPkLen = 112, getBitLvl = 112} 
  | bit_level == "EES761EP2" = ParamSet {getN =  761, getP = 3, getQ = 2048, getDf = 42, getDg = 253, getLLen = 1, getDb = 128, getMaxMsgLenBytes = 125, getBufferLenBits = 1136, getBufferLenTrits = 760, getDm0 = 42, getShaLvl = 1, getDr = 42, getC = 12, getMinCallsR = 13, getMinCallsMask = 16, getOID = [0,3,5], getPkLen = 128, getBitLvl = 128} 
  | bit_level == "EES1087EP1" = ParamSet {getN =  1087, getP = 3, getQ = 2048, getDf = 63, getDg = 362, getLLen = 1, getDb = 192, getMaxMsgLenBytes = 178, getBufferLenBits = 1624, getBufferLenTrits = 1086, getDm0 = 63, getShaLvl = 256, getDr = 63, getC = 13, getMinCallsR = 13, getMinCallsMask = 14, getOID = [0,5,5], getPkLen = 192, getBitLvl = 192} 
  | bit_level == "EES1499EP1" = ParamSet {getN =  1499, getP = 3, getQ = 2048, getDf = 79, getDg = 499, getLLen = 1, getDb = 256, getMaxMsgLenBytes = 247, getBufferLenBits = 2240, getBufferLenTrits = 1498, getDm0 = 79, getShaLvl = 256, getDr = 79, getC = 13, getMinCallsR = 17, getMinCallsMask = 19, getOID = [0,6,5], getPkLen = 256, getBitLvl = 256} 
  | otherwise = error "Unsupported Parameter Set"

-- | The Parameter Set Record
data ParamSet = ParamSet {
  getN :: Int, -- ^ The size of the polynomials
  getP  :: Integer, -- ^ The small modulus p 
  getQ :: Integer, -- ^ The large modulus q
  getDf :: Int, -- ^ The number of 1's in f
  getDg :: Int, -- ^ The number of 1's in g
  getLLen :: Int, -- ^ The length of the encoded message length (should probably be 1)
  getDb :: Int, -- ^ The number of random bits prefixed to the message
  getMaxMsgLenBytes :: Int, -- ^ The max number of bytes in the message
  getBufferLenBits :: Int, -- ^ The size of the resulting message before conversion to trits
  getBufferLenTrits :: Int, -- ^ The size of the resulting message after conversion to trits
  getDm0 :: Int, -- ^ Minimum number of 1's, -1's and 0's in the message for decryption to succeed 
  getShaLvl :: Int, -- ^ SHA algorithm to use. Should be either 1 or 256
  getDr :: Int, -- ^ The number of 1's in the blinding polynomial
  getC :: Int, -- ^ Used by index generator function
  getMinCallsR :: Integer, -- ^ Used by mask generator
  getMinCallsMask :: Int, -- ^ Used by mask generator
  getOID :: [Int], -- ^ Parameter set ID
  getPkLen :: Int, -- ^ Used to create SData
  getBitLvl :: Int -- ^ Bit level security
} deriving (Show)

getSHA :: ParamSet -> ([Integer] -> [Integer])
getSHA params = case (getShaLvl params) of 
  256 -> sha256Octets
  1 -> sha1Octets
  _ -> error "Unsupported SHA function"

getHLen :: ParamSet -> Int
getHLen params = case (getShaLvl params) of
  256 -> 32
  1 -> 20
  _ -> error "Unsupported SHA function"
