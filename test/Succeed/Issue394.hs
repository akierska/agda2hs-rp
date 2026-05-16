GHC compilation failed:
Loaded package environment from /Users/aleksandrakierska/.ghc/aarch64-darwin-9.4.8/environments/default
[1 of 1] Compiling Issue394         ( /var/folders/mr/rp23df650sl4brbf0l4946rr0000gn/T/agda2hs-test-build/Succeed/Issue394.hs, nothing )

/var/folders/mr/rp23df650sl4brbf0l4946rr0000gn/T/agda2hs-test-build/Succeed/Issue394.hs:3:1: error:
    Could not load module ‘Data.ByteString’
    It is a member of the hidden package ‘bytestring-0.11.5.3’.
    You can run ‘:set -package bytestring’ to expose it.
    (Note: this unloads all the modules in the current scope.)
    Use -v (or `:set -v` in ghci) to see a list of the files searched for.
  |
3 | import Data.ByteString (ByteString)
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
