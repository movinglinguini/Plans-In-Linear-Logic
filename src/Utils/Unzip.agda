open import Data.Vec

module Utils.Unzip where

  unzip = ∀ { k } { U V : Vec k } → Vec 2 * k