{- |
	NTRU cryptographic system using the EES1499EP1 parameter set, for use at the 256-bit security level. 
-}

module Math.NTRU.EES1499EP1 (keyGen, encrypt, decrypt) where 

	import qualified Math.NTRU as NTRU 

	-- | Generates a random PublicKey-PrivateKey pair 
	keyGen :: IO ([Integer], [Integer]) -- ^ A tuple representing (PublicKey, PrivateKey) where PrivateKey = 1 + pf, per <https://www.securityinnovation.com/uploads/Crypto/NTRU%20Enhancements%201.pdf enahncement#2>.
	keyGen = NTRU.keyGen (NTRU.genParams "EES1499EP1") 


	-- | Encrypts a message with the given public key
	encrypt :: [Integer] -- ^ A list of ASCII values representing the message
	              -> [Integer] -- ^ A list of numbers representing the public key
	              -> IO [Integer] -- ^ A list of numbers representing the ciphertext
	encrypt = NTRU.encrypt (NTRU.genParams "EES1499EP1")

	-- | Decrypts and verifies a cyphertext with the given keys
	decrypt :: [Integer] -- ^ A list of numbers representing the private key
	              -> [Integer] -- ^ A list of numbers representing the public key
	              -> [Integer] -- ^ A list of numbers representing the ciphertext
	              -> Maybe [Integer] -- ^ A list of numbers representing the original message, or nothing on failure
	decrypt = NTRU.decrypt (NTRU.genParams "EES1499EP1")