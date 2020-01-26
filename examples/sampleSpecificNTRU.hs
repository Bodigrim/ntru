{-
To compile: ghc sampleSpecificNTRU.hs
To run: ./sampleSpecificNTRU
-}

-- Paramter Set EES401EP1
import Math.NTRU.EES401EP1 
import Data.Char
import Data.Maybe

main = do 
	
	(publicKey, privateKey) <- keyGen
	
	let msg = map (fromIntegral . ord) "Hello, World" :: [Integer]

	ct <- encrypt msg publicKey

	let unencrypted = decrypt privateKey publicKey ct 

	if (isNothing unencrypted)
	then print "Encryption Failed"
	else print $ map (chr . fromIntegral) (fromJust unencrypted)

