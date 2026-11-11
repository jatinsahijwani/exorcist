import Verifier.Models.Registry
import Verifier.Models.User

namespace NearAsync.Vault

def allModels : List Model := models ++ userModels

def findModel (n : String) : Option Model := allModels.find? (·.name == n)

end NearAsync.Vault
