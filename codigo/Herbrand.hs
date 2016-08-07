module Herbrand where
import Data.List
import Text.PrettyPrint.GenericPretty
import PFH                           
import LPH                           
import PTLP                          

-- Una signatura es un terna formada po la lista de constantes, de
-- símbolos de función (con su aridad) y los símbolos de relación (con
-- su aridad).
type Signatura = ([Nombre],[(Nombre,Int)],[(Nombre,Int)]) 

-- | (unionSignatura s1 s2) es la unión de las signaturas s1 y s2.
-- Por ejemplo,
-- >>> let s1 = (["a"],[("f",1)],[])
-- >>> let s2 = (["b","c"],[("f",1),("g",2)],[("R",2)])
-- >>> unionSignatura s1 s2
-- (["a","b","c"],[("f",1),("g",2)],[("R",2)])
unionSignatura :: Signatura -> Signatura -> Signatura
unionSignatura (cs1,fs1,rs1) (cs2,fs2,rs2) =
  ( cs1 `union` cs2
  , fs1 `union` fs2
  , rs1 `union` rs2 )

-- | (unionSignaturas ss) es la unión de la lista de signaturas ss.
-- Por ejemplo,
-- >>> let s1 = (["a"],[("f",1)],[])
-- >>> let s2 = (["b","c"],[("f",1),("g",2)],[("R",2)])
-- >>> let s3 = (["a","c"],[],[("P",1)])
-- >>> unionSignaturas [s1,s2,s3]
-- (["a","b","c"],[("f",1),("g",2)],[("R",2),("P",1)])
unionSignaturas :: [Signatura] -> Signatura
unionSignaturas = foldr unionSignatura ([], [], [])

-- | (signaturaTerm t) es la signatura del término t. Por 
-- ejemplo,
-- >>> signaturaTerm tx
-- ([],[],[])
-- >>> signaturaTerm a
-- (["a"],[],[])
-- >>> let t1 = Ter "f" [a,tx,Ter "g" [b,a]]
-- >>> t1
-- f[a,x,g[b,a]]
-- >>> signaturaTerm t1
-- (["a","b"],[("f",3),("g",2)],[])
signaturaTerm :: Termino -> Signatura
signaturaTerm (Var _)    = ([],[],[])
signaturaTerm (Ter c []) = ([c],[],[])
signaturaTerm (Ter f ts) = (cs,[(f,n)] `union` fs,rs) 
  where (cs,fs,rs) = unionSignaturas (map signaturaTerm ts)
        n          = length ts

-- | (signaturaForm t) es la signatura de la fórmula f. Por ejemplo,
-- >>> let f1 = Atom "R" [a,tx,Ter "g" [b,a]]
-- >>> f1
-- R[a,x,g[b,a]]
-- >>> signaturaForm f1
-- (["a","b"],[("g",2)],[("R",3)])
-- >>> signaturaForm (Neg f1)
-- (["a","b"],[("g",2)],[("R",3)])
-- >>> let f2 = Atom "P" [b]
-- >>> let f3 = Impl f1 f2
-- >>> f3
-- (R[a,x,g[b,a]]⟹P[b])
-- >>> signaturaForm f3
-- (["a","b"],[("g",2)],[("R",3),("P",1)])
-- >>> let f4 = Conj [f1,f2,f3]
-- >>> f4
-- (R[a,x,g[b,a]]⋀(P[b]⋀(R[a,x,g[b,a]]⟹P[b])))
-- >>> signaturaForm f4
-- (["a","b"],[("g",2)],[("R",3),("P",1)])
-- >>> let f5 = PTodo x f4
-- >>> f5
-- ∀x (R[a,x,g[b,a]]⋀(P[b]⋀(R[a,x,g[b,a]]⟹P[b])))
-- >>> signaturaForm f5
-- (["a","b"],[("g",2)],[("R",3),("P",1)])
signaturaForm :: Form -> Signatura
signaturaForm (Atom r ts) =
  (cs,fs, [(r,n)] `union` rs)
  where (cs,fs,rs) = unionSignaturas (map signaturaTerm ts)
        n          = length ts
signaturaForm (Neg f) =
  signaturaForm f
signaturaForm (Impl f1 f2) =
  signaturaForm f1 `unionSignatura` signaturaForm f2
signaturaForm (Equiv f1 f2) =
  signaturaForm f1 `unionSignatura` signaturaForm f2
signaturaForm (Conj fs) =
  unionSignaturas (map signaturaForm fs)
signaturaForm (Disy fs) =
  unionSignaturas (map signaturaForm fs)
signaturaForm (PTodo _ f) =
  signaturaForm f
signaturaForm (Ex _ f) =
  signaturaForm f

-- | (signaturaForms ts) es la signatura del conjunto de fórmulas f. Por
-- ejemplo,
-- >>> let f1 = Atom "R" [Ter "f" [tx]]
-- >>> let f2 = Impl f1 (Atom "Q" [a,Ter "f" [b]])
-- >>> let f3 = Atom "S" [Ter "g" [a,b]]
-- >>> signaturaForms [f1,f2,f3]
-- (["a","b"],[("f",1),("g",2)],[("R",1),("Q",2),("S",1)])
signaturaForms :: [Form] -> Signatura
signaturaForms fs =
  unionSignaturas (map signaturaForm fs)

-- | (universoHerbrand n s) es el n-ésimo nivel del universo de Herbrand
-- de la signatura s. Por ejemplo,
-- >>> let s1 = (["a","b","c"],[],[])
-- >>> universoHerbrand 0 s1 
-- [a,b,c]
-- >>> universoHerbrand 1 s1 
-- [a,b,c]
--
-- >>> let s2 = ([],[("f",1)],[])
-- >>> universoHerbrand 0 s2 
-- [a]
-- >>> universoHerbrand 1 s2 
-- [a,f[a]]
-- >>> universoHerbrand 2 s2 
-- [a,f[a],f[f[a]]]
-- 
-- >>> let s3 = (["a","b"],[("f",1),("g",1)],[])
-- >>> universoHerbrand 0 s3 
-- [a,b]
-- >>> universoHerbrand 1 s3 
-- [a,b,f[a],f[b],g[a],g[b]]
-- >>> pp $ universoHerbrand 2 s3 
-- [a,b,f[a],f[b],g[a],g[b],f[f[a]],f[f[b]],f[g[a]],
--  f[g[b]],g[f[a]],g[f[b]],g[g[a]],g[g[b]]]
-- >>> universoHerbrand 3 (["a"],[("f",1)],[("R",1)]) 
-- [a,f[a],f[f[a]],f[f[f[a]]]]
-- >>> pp $ universoHerbrand 3 (["a","b"],[("f",1),("g",1)],[]) 
-- [a,b,f[a],f[b],g[a],g[b],f[f[a]],f[f[b]],f[g[a]],
--  f[g[b]],g[f[a]],g[f[b]],g[g[a]],g[g[b]],f[f[f[a]]],
--  f[f[f[b]]],f[f[g[a]]],f[f[g[b]]],f[g[f[a]]],
--  f[g[f[b]]],f[g[g[a]]],f[g[g[b]]],g[f[f[a]]],
--  g[f[f[b]]],g[f[g[a]]],g[f[g[b]]],g[g[f[a]]],
--  g[g[f[b]]],g[g[g[a]]],g[g[g[b]]]]
-- 
-- >>> let s4 = (["a","b"],[("f",2)],[])
-- >>> universoHerbrand 0 s4
-- [a,b]
-- >>> universoHerbrand 1 s4
-- [a,b,f[a,a],f[a,b],f[b,a],f[b,b]]
-- >>> pp $ universoHerbrand 2 s4 
-- [a,b,f[a,a],f[a,b],f[b,a],f[b,b],f[a,f[a,a]],
--  f[a,f[a,b]],f[a,f[b,a]],f[a,f[b,b]],f[b,f[a,a]],
--  f[b,f[a,b]],f[b,f[b,a]],f[b,f[b,b]],f[f[a,a],a],
--  f[f[a,a],b],f[f[a,a],f[a,a]],f[f[a,a],f[a,b]],
--  f[f[a,a],f[b,a]],f[f[a,a],f[b,b]],f[f[a,b],a],
--  f[f[a,b],b],f[f[a,b],f[a,a]],f[f[a,b],f[a,b]],
--  f[f[a,b],f[b,a]],f[f[a,b],f[b,b]],f[f[b,a],a],
--  f[f[b,a],b],f[f[b,a],f[a,a]],f[f[b,a],f[a,b]],
--  f[f[b,a],f[b,a]],f[f[b,a],f[b,b]],f[f[b,b],a],
--  f[f[b,b],b],f[f[b,b],f[a,a]],f[f[b,b],f[a,b]],
--  f[f[b,b],f[b,a]],f[f[b,b],f[b,b]]]
universoHerbrand :: Int -> Signatura -> [Termino]
universoHerbrand 0 (cs,_,_) 
  | null cs   = [a]
  | otherwise = [Ter c [] | c <- cs]
universoHerbrand n s@(_,fs,_) =
  u `union`
  [Ter f ts | (f,k) <- fs
            , ts <- variacionesR k u]
  where u = universoHerbrand (n-1) s 

-- | (universoHerbrandForm n f) es el n-ésimo nivel del universo de Herbrand
-- de la fórmula f. Por ejemplo,
-- >>> let f1 = Atom "R" [a,b,c]
-- >>> universoHerbrandForm 1 f1
-- [a,b,c]
-- >>> let f2 = Atom "R" [Ter "f" [tx]]
-- >>> universoHerbrandForm 2 f2
-- [a,f[a],f[f[a]]]
-- >>> let f3 = Impl f2 (Atom "Q" [a,Ter "g" [b]])
-- >>> f3
-- (R[f[x]]⟹Q[a,g[b]])
-- >>> pp $ universoHerbrandForm 2 f3
-- [a,b,f[a],f[b],g[a],g[b],f[f[a]],f[f[b]],f[g[a]],
--  f[g[b]],g[f[a]],g[f[b]],g[g[a]],g[g[b]]]
-- >>> let f4 = Atom "R" [Ter "f" [a,b]]
-- >>> signaturaForm f4
-- (["a","b"],[("f",2)],[("R",1)])
-- >>> pp $ universoHerbrandForm 2 f4
-- [a,b,f[a,a],f[a,b],f[b,a],f[b,b],f[a,f[a,a]],
--  f[a,f[a,b]],f[a,f[b,a]],f[a,f[b,b]],f[b,f[a,a]],
--  f[b,f[a,b]],f[b,f[b,a]],f[b,f[b,b]],f[f[a,a],a],
--  f[f[a,a],b],f[f[a,a],f[a,a]],f[f[a,a],f[a,b]],
--  f[f[a,a],f[b,a]],f[f[a,a],f[b,b]],f[f[a,b],a],
--  f[f[a,b],b],f[f[a,b],f[a,a]],f[f[a,b],f[a,b]],
--  f[f[a,b],f[b,a]],f[f[a,b],f[b,b]],f[f[b,a],a],
--  f[f[b,a],b],f[f[b,a],f[a,a]],f[f[b,a],f[a,b]],
--  f[f[b,a],f[b,a]],f[f[b,a],f[b,b]],f[f[b,b],a],
--  f[f[b,b],b],f[f[b,b],f[a,a]],f[f[b,b],f[a,b]],
--  f[f[b,b],f[b,a]],f[f[b,b],f[b,b]]]
universoHerbrandForm :: Int -> Form -> [Termino]
universoHerbrandForm n f =
  universoHerbrand n (signaturaForm f)

-- | (universoHerbrandForms n fs) es el n-ésimo nivel del universo de Herbrand
-- del conjunto de fórmulas f. Por ejemplo,
-- >>> let f1 = Atom "R" [Ter "f" [tx]]
-- >>> let f2 = Impl f1 (Atom "Q" [a,Ter "f" [b]])
-- >>> let f3 = Atom "S" [Ter "g" [a,b]]
-- >>> universoHerbrandForms 1 [f1,f2,f3]
-- [a,f[a],b,f[b],g[a,a],g[a,b],g[b,a],g[b,b]]
universoHerbrandForms :: Int -> [Form] -> [Termino]
universoHerbrandForms n fs =
  nub (concatMap (universoHerbrandForm n) fs)

-- | Las bases de Herbrand son conjuntos de fórmulas
type BaseH = [Form]

-- | (baseHerbrand n s) es el n-ésimo nivel de la base de Herbrand
-- de la signatura s. Por ejemplo,
-- >>> let s1 = (["a","b","c"],[],[("P",1)])
-- >>> baseHerbrand 0 s1
-- [P[a],P[b],P[c]]
-- >>> let s2 = (["a","b","c"],[],[("P",1),("Q",1),("R",1)])
-- >>> let s2 = (["a","b","c"],[("f",1)],[("P",1),("Q",1),("R",1)])
-- >>> baseHerbrand 0 s2
-- [P[a],P[b],P[c],Q[a],Q[b],Q[c],R[a],R[b],R[c]]
-- >>> pp $ baseHerbrand 1 s2
-- [P[a],P[b],P[c],P[f[a]],P[f[b]],P[f[c]],Q[a],Q[b],
--  Q[c],Q[f[a]],Q[f[b]],Q[f[c]],R[a],R[b],R[c],R[f[a]],
--  R[f[b]],R[f[c]]]
baseHerbrand :: Int -> Signatura -> BaseH
baseHerbrand n s@(_,_,rs) =
  [Atom r ts | (r,k) <- rs
             , ts <- variacionesR k u]
  where u = universoHerbrand n s

-- | (baseHerbrandForm n f) es el n-ésimo nivel de la base de Herbrand
-- de la fórmula f. Por ejemplo,
-- >>> let f1 = Atom "P" [Ter "f" [tx]]
-- >>> f1
-- P[f[x]]
-- >>> baseHerbrandForm 2 f1
-- [P[a],P[f[a]],P[f[f[a]]]]
baseHerbrandForm :: Int -> Form -> BaseH
baseHerbrandForm n f =
  baseHerbrand n (signaturaForm f)

-- | (baseHerbrandForms n f) es el n-ésimo nivel de la base de Herbrand
-- de la fórmula f. Por ejemplo,
-- >>> let f1 = Atom "P" [Ter "f" [tx]]
-- >>> let f2 = Atom "Q" [Ter "g" [b]]
-- >>> baseHerbrandForms 1 [f1,f2]
-- [P[b],P[f[b]],P[g[b]],Q[b],Q[f[b]],Q[g[b]]]
baseHerbrandForms :: Int -> [Form] -> BaseH
baseHerbrandForms n fs =
  baseHerbrandForm n (Conj fs)

type UniversoH = Universo Termino

type InterpretacionHR = InterpretacionR Termino

type InterpretacionHF = InterpretacionF Termino

type InterpretacionH = (InterpretacionHR, InterpretacionHF)  

-- AtomosH representan conjuntos de fórmulas atómicas básicas (es decir,
-- subconjuntos de bases de Herbrand).
type AtomosH = [Form]

-- | (interpretacionH fs) es la interpretación de Herbrand
-- correspondiente al conjunto de átomos de Herbrand H. 
-- >>> let f1 = Atom "P" [a]
-- >>> let f2 = Atom "P" [Ter "f" [a,b]]
-- >>> let fs = [f1,f2]
-- >>> let (iR,iF) = interpretacionH fs
-- >>> iF "f" [a,c]
-- f[a,c]
-- >>> iR "P" [a]
-- True
-- >>> iR "P" [b]
-- False
-- >>> iR "P" [Ter "f" [a,b]]
-- True
-- >>> iR "P" [Ter "f" [a,a]]
-- False
interpretacionH :: AtomosH -> InterpretacionH
interpretacionH fs = (iR,iF)
  where iF f ts   = Ter  f ts
        iR r ts   = Atom r ts `elem` fs

valorH :: UniversoH -> InterpretacionH -> Form -> Bool
valorH u i f =
  valorF u i s f
  where s _ = a

-- (modelosHForm n f) son los subconjuntos del n-ésimo nivel de la base de
-- Herbrand de la fórmula f que son modelos de f. Por ejemplo,
-- >>> let f1 = Disy [Atom "P" [a], Atom "P" [b]]
-- >>> f1
-- (P[a]⋁P[b])
-- >>> modelosHForm 0 f1
-- [[P[a]],[P[b]],[P[a],P[b]]]
-- >>> let f2 = Impl (Atom "P" [a]) (Atom "P" [b])
-- >>> f2
-- (P[a]⟹P[b])
-- >>> modelosHForm 0 f2
-- [[],[P[b]],[P[a],P[b]]]
-- >>> let f3 = Conj [Atom "P" [a], Atom "P" [b]]
-- >>> f3
-- (P[a]⋀P[b])
-- >>> modelosHForm 0 f3
-- [[P[a],P[b]]]
-- >>> let f4 = PTodo x (Impl (Atom "P" [tx]) (Atom "Q" [Ter "f" [tx]]))
-- >>> f4
-- ∀x (P[x]⟹Q[f[x]])
-- >>> modelosHForm 0 f4
-- [[],[Q[a]]]
-- >>> modelosHForm 1 f4
-- [[],[Q[a]],[Q[f[a]]],[P[a],Q[f[a]]],[Q[a],Q[f[a]]],[P[a],Q[a],Q[f[a]]]]
-- >>> length (modelosHForm 2 f4)
-- 18
modelosHForm :: Int -> Form -> [AtomosH]
modelosHForm n f =
  [fs | fs <- subsequences bH
      , valorH uH (interpretacionH fs) f]
  where uH = universoHerbrandForm n f
        bH = baseHerbrandForm n f

-- (modelosH n fs) son los subconjuntos del n-ésimo nivel de la base de
-- Herbrand del conjunto de fórmulas f que son modelos de fs. Por ejemplo,
-- >>> let f1 = PTodo x (Impl (Atom "P" [tx]) (Atom "Q" [Ter "f" [tx]]))
-- >>> f1
-- ∀x (P[x]⟹Q[f[x]])
-- >>> let f2 = Ex x (Atom "P" [tx])
-- >>> f2
-- ∃x P[x]
-- >>> modelosH 0 [f1,f2]
-- []
-- >>> modelosH 1 [f1,f2]
-- [[P[a],Q[f[a]]],[P[a],Q[a],Q[f[a]]]]
modelosH :: Int -> [Form] -> [AtomosH]
modelosH n fs =
  [gs | gs <- subsequences bH
      , and [valorH uH (interpretacionH gs) f | f <- fs]]
  where uH = universoHerbrandForms n fs
        bH = baseHerbrandForms n fs

-- La validación es
--    codigo> doctest Herbrand.hs 
--    Examples: 119  Tried: 119  Errors: 0  Failures: 0
