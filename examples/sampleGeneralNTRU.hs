{-
To compile: ghc sampleGeneralNTRU.hs
To run: ./sampleGeneralNTRU
-}

import Math.NTRU
import Data.Char
import Data.Maybe

main = do 
	
--  let params = genParams "EES401EP1" 
	let params = ParamSet {getN =  401, getP = 3, getQ = 2048, getDf = 113, getDg = 133, getLLen = 1, getDb = 112, getMaxMsgLenBytes = 60, getBufferLenBits = 600, getBufferLenTrits = 400, getDm0 = 113, getShaLvl = 1, getDr = 113, getC = 11, getMinCallsR = 32, getMinCallsMask = 9, getOID = [0,2,4], getPkLen = 114, getBitLvl = 112}

	(publicKey, privateKey) <- keyGen params
	
	let msg = map (fromIntegral . ord) "Hello, World" :: [Integer]

	ct <- encrypt params msg publicKey

	let unencrypted = decrypt params privateKey publicKey ct 

	if (isNothing unencrypted)
	then print "Encryption Failed"
	else print $ map (chr . fromIntegral) (fromJust unencrypted)

