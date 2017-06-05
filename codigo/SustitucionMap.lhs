\begin{code}
module SustDiccionario where
import LPH
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty
\end{code}

Debido a que muchas funciones de esta librería coinciden
con funciones definidas en \texttt{Prelude}, ésta se suele
importar \texttt{qualified}.

\comentario{No compatible con nuestra definición de término, hay que adaptarlo}
