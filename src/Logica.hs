-- Module      : Logica
-- Description : Sintaxis y semántica de la lógica proposicional
-- Copyright   : José A. Alonso
-- License     : GPL-3
-- Maintainer  : JoseA.Alonso@gmail.com
-- Stability   : Provisional

module Logica where

-- ---------------------------------------------------------------------
-- Librerías auxiliares                                               --
-- ---------------------------------------------------------------------

import Control.Monad ( liftM
                     , liftM2)
import Data.List     ( union
                     , subsequences
                     )
import Test.QuickCheck

-- ---------------------------------------------------------------------
-- * Sintaxis de fórmulas proposicionales
-- ---------------------------------------------------------------------

-- | Los símbolos proposicionales se representan por cadenas.
type SimboloProposicional = String

-- | FProp es el tipo de las fórmulas proposicionales definidas por
-- 
-- * T y F son fórmulas
-- * Si A es una fórmula, también lo es ¬A.
-- * Si A y B son fórmulas, entonces (A ∧ B), (A ∨ B), (A → B) y
--   (A ↔ B) también lo son.
data FProp = T
           | F
           | Atom SimboloProposicional
           | Neg FProp 
           | Conj FProp FProp 
           | Disj FProp FProp 
           | Impl FProp FProp 
           | Equi FProp FProp 
  deriving (Eq,Ord)

-- | Declaración del procedimiento de escritura de fórmulas.
instance Show FProp where
    show (T)        = "⊤"
    show (F)        = "⊥"
    show (Atom x)   = x
    show (Neg x)    = "¬" ++ show x
    show (Conj x y) = "(" ++ show x ++ " ∧ " ++ show y ++ ")"
    show (Disj x y) = "(" ++ show x ++ " ∨ " ++ show y ++ ")"
    show (Impl x y) = "(" ++ show x ++ " → " ++ show y ++ ")"
    show (Equi x y) = "(" ++ show x ++ " ↔ " ++ show y ++ ")"

-- ** Ejemplos de fórmulas atómicas

-- | Ejemplo de fórmulas.
p, q, r :: FProp
p  = Atom "p"
q  = Atom "q"
r  = Atom "r"

-- ** Conectivas lógicas

-- | (no f) es la negación de f 
no :: FProp -> FProp
no = Neg

-- | (f ∨ g) es la disyunción de f y g.
(∨) :: FProp -> FProp -> FProp
(∨)   = Disj
infixr 5 ∨

-- | (f ∧ g) es la conjunción de f y g
(∧) :: FProp -> FProp -> FProp
(∧)   = Conj
infixr 4 ∧

-- | (f → g) es la implicación de f a g
(→) :: FProp -> FProp -> FProp
(→)  = Impl
infixr 3 →

-- | (f ↔ g) es la equivalencia entre f y g
(↔) :: FProp -> FProp -> FProp
(↔) = Equi
infixr 2 ↔

-- ---------------------------------------------------------------------
-- Generadores de fórmulas proposicionales 
-- ---------------------------------------------------------------------

-- | FProp es una instancia de Arbitrary. Por ejemplo,
--
-- @
--    > sample (arbitrary :: Gen FProp)
--    T
--    (no p ∨ (F ∧ F))
--    no r
--    ((q → (T ∧ s)) → F)
--    ((((T → p) ∧ s) → no (q → q)) → s)
--    ((no (r ∨ r) → no (p → s)) ∧ ((p ↔ T) ∧ no (s ↔ F)))
--    (F → s)
--    no no p
-- @
instance Arbitrary FProp where
  arbitrary = sized prop
    where
      prop n  | n <= 0     = atom
              | otherwise  = oneof [ 
                    atom
                    , liftM Neg subform
                    , liftM2 Conj subform  subform
                    , liftM2 Disj subform  subform
                    , liftM2 Impl subform  subform
                    , liftM2 Equi subform' subform' ]
        where
          atom     = oneof [liftM Atom (elements ["p","q","r","s"]),
                            elements [F,T]]
          subform  = prop ( n `div` 2)
          subform' = prop ( n `div` 4)

-- ---------------------------------------------------------------------
-- * Semántica de la lógica proposicional
-- ---------------------------------------------------------------------

-- | Las interpretaciones son listas de fórmulas atómicas. Las fórmulas
-- de las interpretaciones se suponen verdaderas y las restantes
-- fórmulas atómicas se suponen falsas.
type Interpretacion = [FProp]

-- | (significado f i) es el significado de la fórmula f en la
-- interprestación i. Por ejemplo, 
-- 
-- >>> significado ((p ∨ q) ∧ ((no q) ∨ r)) [r]
-- False
-- >>> significado ((p ∨ q) ∧ ((no q) ∨ r)) [p,r]
-- True
significado :: FProp -> Interpretacion -> Bool
significado T          _ = True
significado F          _ = False
significado (Atom f)   i = (Atom f) `elem` i
significado (Neg f)    i = not (significado f i)
significado (Conj f g) i = (significado f i) && (significado g i)
significado (Disj f g) i = (significado f i) || (significado g i)
significado (Impl f g) i = significado (Disj (Neg f) g) i
significado (Equi f g) i = significado (Conj (Impl f g) (Impl g f)) i

-- ---------------------------------------------------------------------
-- * Modelos de una fórmula
-- ---------------------------------------------------------------------

-- | (simbolosPropForm f) es el conjunto formado por todos los símbolos
-- proposicionales que aparecen en f. Por ejemplo, 
-- 
-- >>> simbolosPropForm (p ∧ q → p)
-- [p,q]
simbolosPropForm :: FProp -> [FProp]
simbolosPropForm T          = []
simbolosPropForm F          = []
simbolosPropForm (Atom f)   = [(Atom f)]
simbolosPropForm (Neg f)    = simbolosPropForm f
simbolosPropForm (Conj f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Disj f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Impl f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Equi f g) = simbolosPropForm f `union` simbolosPropForm g

-- | (interpretacionesForm f) es la lista de todas las interpretaciones de
-- la fórmula f. Por ejemplo,
--
-- >>> interpretacionesForm (p ∧ q → p)
-- [[],[p],[q],[p,q]]
interpretacionesForm :: FProp -> [Interpretacion]
interpretacionesForm f = subsequences (simbolosPropForm f)

-- | (esModeloFormula i f) se verifica si la interpretación i es un modelo
-- de la fórmula f. Por ejemplo, 
--
-- >>> esModeloFormula [r]   ((p ∨ q) ∧ ((no q) ∨ r))
-- False
-- >>> esModeloFormula [p,r] ((p ∨ q) ∧ ((no q) ∨ r))
-- True
esModeloFormula :: Interpretacion -> FProp -> Bool
esModeloFormula i f = significado f i

-- | (modelosFormula f) es la lista de todas las interpretaciones de la
-- fórmula f que son modelo de F. Por ejemplo,
--
-- >>> modelosFormula ((p ∨ q) ∧ ((no q) ∨ r)) 
-- [[p],[p,r],[q,r],[p,q,r]]
modelosFormula :: FProp -> [Interpretacion]
modelosFormula f =
  [i | i <- interpretacionesForm f
     , esModeloFormula i f]

-- ---------------------------------------------------------------------
-- * Fórmulas válidas, satisfacibles e insatisfacibles
-- ---------------------------------------------------------------------

-- | (esValida f) se verifica si la fórmula f es válida. Por ejemplo,
--
-- >>> esValida (p → p)
-- True
-- >>> esValida (p → q)
-- False
-- >>> esValida ((p → q) ∨ (q → p))
-- True
esValida :: FProp -> Bool
esValida f = 
  modelosFormula f == interpretacionesForm f

-- | (prop_esValida f) se verifica si las siguiente condiciones son
-- equivalentes:
--
-- * f es válida
-- * f es consecuencia del conjunto vacío.
--
-- >>> quickCheck prop_esValida
-- +++ OK, passed 100 tests.
prop_esValida :: FProp -> Bool
prop_esValida f =
   esValida f == esConsecuencia [] f

-- | (esInsatisfacible f) se verifica si la fórmula f es insatisfacible. 
-- Por ejemplo,
--
-- >>> esInsatisfacible (p ∧ (no p))
-- True
-- >>> esInsatisfacible ((p → q) ∧ (q → r))
-- False
esInsatisfacible :: FProp -> Bool
esInsatisfacible f =
  modelosFormula f == []

-- | (esSatisfacible f) se verifica si f es satisfacible. Por ejemplo,
--
-- >>> esSatisfacible (p ∧ (no p))
-- False
-- >>> esSatisfacible ((p → q) ∧ (q → r))
-- True
esSatisfacible :: FProp -> Bool
esSatisfacible f =
  modelosFormula f /= []

-- ---------------------------------------------------------------------
-- * Interpretaciones de un conjunto de fórmulas
-- ---------------------------------------------------------------------

-- | (unionGeneral x) es la unión de los conjuntos de la lista de
-- conjuntos x. Por ejemplo,
--
-- >>> unionGeneral []
-- []
-- >>> unionGeneral [[1]]
-- [1]
-- >>> unionGeneral [[1],[1,2],[2,3]]
-- [1,2,3]
unionGeneral :: Eq a => [[a]] -> [a]
unionGeneral = foldr union []

-- | (simbolosPropConj s) es el conjunto de los símbolos proposiciones de 
-- s. Por ejemplo,
--
-- >>> simbolosPropConj [p ∧ q → r, p → r]
-- [p,q,r]
simbolosPropConj :: [FProp] -> [FProp]
simbolosPropConj s =
  unionGeneral [simbolosPropForm f | f <- s]

-- | (interpretacionesConjunto s) es la lista de las interpretaciones de 
-- s. Por ejemplo,
--
-- >>> interpretacionesConjunto [p → q, q → r]
-- [[],[p],[q],[p,q],[r],[p,r],[q,r],[p,q,r]]
interpretacionesConjunto :: [FProp] -> [Interpretacion]
interpretacionesConjunto s =
  subsequences (simbolosPropConj s)

-- ---------------------------------------------------------------------
-- * Modelos de conjuntos de fórmulas
-- ---------------------------------------------------------------------

-- | (esModeloConjunto i s) se verifica si i es modelo de s. Por
-- ejemplo,
--
-- >>> esModeloConjunto [p,r] [(p ∨ q) ∧ ((no q) ∨ r), q → r]
-- True
-- >>> esModeloConjunto [p,r] [(p ∨ q) ∧ ((no q) ∨ r), r → q]
-- False
esModeloConjunto :: Interpretacion -> [FProp] -> Bool
esModeloConjunto i s =
  and [esModeloFormula i f | f <- s]

-- | (modelosConjunto s) es la lista de modelos del conjunto s. 
-- Por ejemplo,
--
-- >>> modelosConjunto [(p ∨ q) ∧ ((no q) ∨ r), q → r]
-- [[p],[p,r],[q,r],[p,q,r]]
-- >>> modelosConjunto [(p ∨ q) ∧ ((no q) ∨ r), r → q]
-- [[p],[q,r],[p,q,r]]
modelosConjunto :: [FProp] -> [Interpretacion]
modelosConjunto s =
  [i | i <- interpretacionesConjunto s
     , esModeloConjunto i s]

-- ---------------------------------------------------------------------
-- * Conjuntos consistentes e inconsistentes de fórmulas
-- ---------------------------------------------------------------------

-- | (esConsistente s) se verifica si s es consistente. Por ejemplo,
--
-- >>> esConsistente [(p ∨ q) ∧ ((no q) ∨ r), p → r]        
-- True
-- >>> esConsistente [(p ∨ q) ∧ ((no q) ∨ r), p → r, no r]  
-- False
esConsistente :: [FProp] -> Bool
esConsistente s =
  modelosConjunto s /= []

-- | (esInconsistente s) se verifica si s es inconsistente. Por ejemplo,
--
-- >>> esInconsistente [(p ∨ q) ∧ ((no q) ∨ r), p → r]        
-- False
-- >>> esInconsistente [(p ∨ q) ∧ ((no q) ∨ r), p → r, no r]  
-- True
esInconsistente :: [FProp] -> Bool
esInconsistente s =
  modelosConjunto s == []

-- ---------------------------------------------------------------------
-- * Consecuencia lógica
-- ---------------------------------------------------------------------

-- | (esConsecuencia s f) se verifica si f es consecuencia de s. Por 
-- ejemplo,
--
-- >>> esConsecuencia [p → q, q → r] (p → r)
-- True
-- >>> esConsecuencia [p] (p ∧ q)
-- False
esConsecuencia :: [FProp] -> FProp -> Bool
esConsecuencia s f =
  null [i | i <- interpretacionesConjunto (f:s)
          , esModeloConjunto i s
          , not (esModeloFormula i f)]

-- | (prop_esConsecuencia s f) verifica que son equivalentes:
--
-- * f es consecuencia de s
-- * s ∪ {¬f} es inconsistente
--
-- >>> quickCheck prop_esConsecuencia
-- +++ OK, passed 100 tests.
prop_esConsecuencia :: [FProp] -> FProp -> Bool
prop_esConsecuencia s f =
   esConsecuencia s f == esInconsistente (Neg f:s)

-- ---------------------------------------------------------------------
-- * Equivalencia de fórmulas
-- ---------------------------------------------------------------------

-- | (equivalentes f g) se verifica si las fórmulas f y g son
-- equivalentes. Por ejemplo,
--
-- >>> equivalentes (p → q) (no p ∨ q)
-- True
equivalentes :: FProp -> FProp -> Bool
equivalentes f g = esValida (f ↔ g)
