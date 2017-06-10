module SustMap where
import LPH
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty


-- Sustitución de términos:
sustTerm :: Termino -> Map Variable Termino -> Termino
sustTerm (Var x) d = aux  x (M.lookup x d)
    where
      aux x (Just n) = n
      aux x Nothing = Var x
susTerm (Ter f ts) d = Ter f (sustTerms ts d)

-- Sustitución de una lista de términos:
sustTerms :: [Termino] -> Map Variable Termino -> [Termino]
sustTerms [] d = []
sustTerms (t:ts) d = (sustTerm t d):(sustTerms ts d)


-- Sustitución de términos en fórmulas:

sustitucion :: Form -> Map Variable Termino -> Form 
sustitucion (Atom str ts) d = Atom str (sustTerms ts d)
sustitucion (Ig t1 t2) d = Ig (sustTerm t1 d) (sustTerm t2 d)
sustitucion  (Neg f) d = Neg (sustitucion f d)
sustitucion (Impl f1 f2) d =
  Impl (sustitucion f1 d) (sustitucion f2 d)
sustitucion (Equiv f1 f2) d =
  Equiv (sustitucion f1 d) (sustitucion f2 d)
sustitucion (Conj fs) d = Conj (aux fs d)
    where
      aux fs d = [sustitucion f d | f <- fs]
sustitucion (Disy fs) d = Disy (aux fs d)
    where
      aux fs d = [sustitucion f d | f <- fs]
sustitucion (PTodo v f) d = PTodo v (sustitucion f (M.delete v d))
sustitucion (Ex v f) d = Ex v (sustitucion f (M.delete v d))

-- Ejemplo:
-- λ> formula3
-- (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
-- λ> let sust = M.fromList [(x,ty),(y,tx),(z,tx)]
-- λ> sustitucion formula3 sust
-- (R[y,x]⟹∃z (R[y,z]⋀R[z,x]))
