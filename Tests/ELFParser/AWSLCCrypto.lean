import Tests.ELFParser.SymbolContents

def CryptoELF := (getELFFile (System.mkFilePath ["Tests", "ELFParser", "Data", "crypto_test"]))

/--
info: true -/
#guard_msgs in
#eval do (pure (← CryptoELF).is64Bit)

/--
info: false -/
#guard_msgs in
#eval do (pure (← CryptoELF).isBigendian)
