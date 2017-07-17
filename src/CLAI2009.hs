-- CLAI2009.hs
-- Sistema certificado de decisión proposicional basado en polinomios.
-- ---------------------------------------------------------------------

{-|
Module      : CLAI2009
Description : Sistema certificado de decisión proposicional basado en polinomios.
Copyright   : José A. Alonso
License     : GPL-3
Maintainer  : JoseA.Alonso@gmail.com
Stability   : experimental

Código correspondiente al artículo "Sistema certificado de decisión
proposicional basado en polinomios" presentado en el CLAI2009 (Workshop
on Computational Logic and Artificial Intelligence).
-}

module CLAI2009 where

-- ---------------------------------------------------------------------
-- Librerías auxiliares                                               --
-- ---------------------------------------------------------------------

import Control.Monad (liftM,liftM2)
import Data.Char
import Data.List 
import Test.QuickCheck

-- =====================================================================
-- * Lógica
-- =====================================================================

-- ---------------------------------------------------------------------
-- ** Sintaxis de fórmulas proposicionales
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

-- *** Ejemplos de fórmulas atómicas

-- | Ejemplo de fórmulas.
p, q, r :: FProp
p  = Atom "p"
q  = Atom "q"
r  = Atom "r"

-- *** Conectivas lógicas

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
-- ** Semántica de la lógica proposicional
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
-- ** Modelos de una fórmula
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
-- ** Fórmulas válidas, satisfacibles e insatisfacibles
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
-- ** Interpretaciones de un conjunto de fórmulas
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
-- ** Modelos de conjuntos de fórmulas
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
-- ** Conjuntos consistentes e inconsistentes de fórmulas
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
-- ** Consecuencia lógica
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
-- ** Equivalencia de fórmulas
-- ---------------------------------------------------------------------

-- | (equivalentes f g) se verifica si las fórmulas f y g son
-- equivalentes. Por ejemplo,
--
-- >>> equivalentes (p → q) (no p ∨ q)
-- True
equivalentes :: FProp -> FProp -> Bool
equivalentes f g = esValida (f ↔ g)

-- =====================================================================
-- * Polinomios en Z2/(x1^1-x1,...,xn^2-xn)
-- =====================================================================

-- ---------------------------------------------------------------------
-- ** Variables
-- ---------------------------------------------------------------------

-- | 'caracteres' es un generador de caracteres de letras minúsculas. Por
-- ejemplo,
--
-- @
--    > sample caracteres
--    'x'
--    'n'
--    'r'
-- @
caracteres :: Gen Char
caracteres = chr `fmap` choose (97,122)

-- | Las variables se representan por cadenas.
type Variable = String

-- | 'variables' es un generador de variables de longitud 1 ó 2. Por
-- ejemplo,
--
-- @
--    > sample variables
--    "h"
--    "yi"
--    "m"
-- @
variables :: Gen String
variables = do k <- choose (1,2)
               vectorOf k caracteres

-- | variables' es un generador de variables de longitud aleatoria, pero
-- no cero. Por ejemplo,
--
-- @
--    > sample variables'
--    "o"
--    "rte"
--    "tmzeu"
-- @
variables' :: Gen String
variables' = listOf1 caracteres

-- ---------------------------------------------------------------------
-- ** Monomios
-- ---------------------------------------------------------------------

-- | Los monomios son productos de variables distintas y se representan por
-- listas ordenadas de variables distintas. 
data Monomio = M [Variable] 
  deriving (Eq, Ord)

-- | Los monomios se escribe incercalando el * entre sus variables. Por
-- ejemplo,
--
-- >>> M []
-- 1
-- >>> M ["x"]
-- x
-- >>> M ["xy","z","u"] 
-- xy*z*u
instance Show Monomio where
  show (M [])     = "1"
  show (M [v])    = v
  show (M (v:vs)) = concat [v, "*", show (M vs)]

-- | El monomio correspondiente a la lista vacía es el 1 (elemento neutro
-- del producto).
--
-- >>> mUno
-- 1
mUno :: Monomio
mUno = M []

-- | La condición de que las variables sean distintas y ordenadas no se
-- recoge en la definición del tipo de dato. Por ello se define el
-- siguiente reconocedor de monomios. Por ejemplo,
-- 
-- >>> esMonomio (M ["x1","x3","z"])
-- True
-- >>> esMonomio (M ["x5","x3","z"])
-- False
-- >>> esMonomio (M ["x1","x1","z"])
-- False
esMonomio :: Monomio -> Bool
esMonomio (M vs) = vs == sort (nub vs)

-- | (monomiosN n) es un generador de monomios con el número de variables
-- entre 0 y n. Por ejemplo,
--
-- @
--    > sample (monomiosN 3)
--    1
--    s
--    e*t
--    hx*w*xn
--    > sample (monomiosN 10)
--    at*b*dy*fq*gv*mx*y*z
--    a*cm*d*f*h*wf*z
--    b*dw*wx*x*y*z
-- @
monomiosN :: Int -> Gen Monomio
monomiosN n = do k <- choose (0,n)
                 vs <- vectorOf k variables
                 return (M (sort (nub vs)))

-- | monomios es un generador de monomios con el número de variables
-- entre 0 y 3. Por ejemplo,
--
-- @
--    > sample monomios
--    nd*q
--    e
--    1
-- @
monomios :: Gen Monomio
monomios = monomiosN 3

-- | monomios' es un generador de monomios con un número aleatorio de
-- variables. Por ejemplo,
--
-- @
--    > sample monomios'
--    1
--    kl*o*u
--    bm*d*k*mk
-- @
monomios' :: Gen Monomio
monomios' = do xs <- listOf variables
               return (M (sort (nub xs)))

-- | prop_MonomiosGeneraMonomios comprueba que el generador de monomios
-- genera monomios. Por ejemplo,
-- 
-- >>> quickCheck prop_MonomiosGeneraMonomios
-- +++ OK, passed 100 tests.
prop_MonomiosGeneraMonomios :: Monomio -> Bool
prop_MonomiosGeneraMonomios m = esMonomio m

-- Los monomios son arbitrarios.
instance Arbitrary Monomio where
  arbitrary = monomios

-- ---------------------------------------------------------------------
-- ** Polinomios
-- ---------------------------------------------------------------------

-- | Los polinomios son sumas de monomios distintos y ordenados y se
-- representan por listas ordenadas de monomios distintos, 
data Polinomio = P [Monomio]
  deriving (Eq, Ord)

-- | Los polinomios se escribe incercalando el + entre sus monomios. Por
-- ejemplo,
--
-- >>> P [M ["xy","z","u"], M ["p","q"]] 
-- xy*z*u+p*q
-- >>> P [M ["xy","z","u"]] 
-- xy*z*u
-- >>> P [M []] 
-- 1
-- >>> P []
-- 0
instance Show Polinomio where
  show (P [])     = "0"
  show (P [m])    = show m
  show (P (m:ms)) = concat [show m, "+", show (P ms)]

-- | El polinomio correspondiente a la lista vacía es el 0 (elemento
-- neutro de la suma). Por ejemplo,
-- 
-- >>> cero
-- 0
cero :: Polinomio
cero = P []

-- | El polinomio 1 es el polinomio cuyo único elemento es el monomio
-- uno. Por ejemplo,
--
-- >>> uno
-- 1
uno  :: Polinomio
uno = P [mUno]

-- | La condición de que los monomios sean distintos y ordenados no se
-- recoge en la definición del tipo de dato. Por ello se define el
-- siguiente reconocedor de polinomios. Por ejemplo,
-- 
-- >>> esPolinomio (P [M ["a","b","c"], M ["x","y"]])
-- True
-- >>> esPolinomio (P [M ["x","y"], M ["a","c","d"]])
-- False
-- >>> esPolinomio (P [M ["x","y"], M ["a","d","c"]])
-- False
-- >>> esPolinomio (P [M ["x","y"], M ["a","a","c"]])
-- False
-- >>> esPolinomio (P [M ["x","y"], M ["x","y"], M ["a","c","d"]])
-- False
-- >>> esPolinomio (P [M ["a","a","c"], M ["x","y"]])
-- False
esPolinomio :: Polinomio -> Bool
esPolinomio (P ms) =
  all esMonomio ms && ms == sort (nub ms)

-- | (polinomiosN n) es un generador de polinomios con el número de monomios
-- entre 0 y n. Por ejemplo,
--
-- @
--    > sample (polinomiosN 3)
--    0
--    pp*sa
--    gn*nf*zg
--    > sample (polinomiosN 10)
--    1+b*j+gw*w*zm+j*ox+l*q*qz+ly*p*r+m+q*zy
--    iz
--    1+d+dy+jd*l+lr+w
-- @
polinomiosN :: Int -> Gen Polinomio
polinomiosN n = do k <- choose (0,n)
                   ms <- vectorOf k monomios
                   return (P (sort (nub ms)))

-- | polinomios es un generador de polinomios con el número de monomios
-- entre 0 y 3. Por ejemplo,
--
-- @
--    > sample monomios
--    nd*q
--    e
--    1
-- @
polinomios :: Gen Polinomio
polinomios = polinomiosN 3

-- | polinomios' es un generador de polinomios con un número aleatorio de
-- monomios. Por ejemplo,
--
-- @
--    > sample polinomios'
--    0
--    1
--    f*m*on*tr*ue*x
--    ct*d*ds*gy*ps*s*y
-- @
polinomios' :: Gen Polinomio
polinomios' = do xs <- listOf1 monomios
                 return (P (sort (nub xs)))

-- | prop_PolinomiosGeneraPolinomios comprueba que el generador de
-- polinomios genera polinomios. Por ejemplo,
-- 
-- >>> quickCheck prop_PolinomiosGeneraPolinomios
-- +++ OK, passed 100 tests.
prop_PolinomiosGeneraPolinomios :: Polinomio -> Bool
prop_PolinomiosGeneraPolinomios p = esPolinomio p

-- Los polinomios son arbitrarios.
instance Arbitrary Polinomio where
  arbitrary = polinomios

-- Para facilitar la escritura, se hace Polinomio una instancia de
-- la clase Num. Las funciones suma y producto se definen a continuación.
instance Num Polinomio where
  (+) = suma 
  (*) = producto
  (-) = suma
  abs = undefined
  signum = undefined
  fromInteger = undefined

-- ---------------------------------------------------------------------
-- ** Suma de polinomios 
-- ---------------------------------------------------------------------

-- | (suma p q) es la suma de los polinomios p y q. Por ejemplo,
--
-- >>> suma (P [M ["x"], M ["y"]]) (P [M ["y"], M ["z"]]) 
-- x+z
-- >>> suma (P [M ["x"], M ["y"]]) (P [M ["a"], M ["z"]]) 
-- a+x+y+z
suma :: Polinomio -> Polinomio -> Polinomio
suma (P []) (P q) = (P q)
suma (P p)  (P q) = P (sumaAux p q)

-- | (sumaAux xs ys) es la lista de las sumas de los monomios de xs e
-- ys. Por ejemplo,
--
-- >>> sumaAux [M ["x"], M ["y"]] [M ["y"], M ["z"]] 
-- [x,z]
-- >>> sumaAux [M ["x"], M ["y"]] [M ["a"], M ["z"]]
-- [a,x,y,z]
sumaAux :: [Monomio] -> [Monomio] -> [Monomio]
sumaAux [] ys      = ys
sumaAux (x:xs) ys
    | x `elem` ys = sumaAux xs (delete x ys)
    | otherwise  = insert x (sumaAux xs ys)

-- | Comprueba que la suma de polinomios está bien definida.
--
-- >>> quickCheck prop_suma_bien_definida
-- +++ OK, passed 100 tests.
prop_suma_bien_definida :: Polinomio -> Polinomio -> Bool
prop_suma_bien_definida p q = esPolinomio (p+q)

-- | Comprueba que la suma de polinomios es conmutativa.
--
-- >>> quickCheck prop_suma_conmutativa
-- +++ OK, passed 100 tests.
prop_suma_conmutativa :: Polinomio -> Polinomio -> Bool
prop_suma_conmutativa p q = p+q == q+p

-- | Comprueba que la suma de polinomios es conmutativa.
--
-- >>> quickCheck prop_suma_asociativa
-- +++ OK, passed 100 tests.
prop_suma_asociativa :: Polinomio -> Polinomio -> Polinomio -> Bool
prop_suma_asociativa p q r = p+(q+r) == (p+q)+r

-- | Comprueba que cero es el elemento neutro de la suma de polinomios.
--
-- >>> quickCheck prop_suma_neutro
-- +++ OK, passed 100 tests.
prop_suma_neutro :: Polinomio -> Bool
prop_suma_neutro p = p + cero == p

-- | Comprueba que cada elemento es su simétrico en la suma de polinomios.
--
-- >>> quickCheck prop_suma_simetrico
-- +++ OK, passed 100 tests.
prop_suma_simetrico :: Polinomio -> Bool
prop_suma_simetrico p = p+p == cero

-- ---------------------------------------------------------------------
-- ** Productos de polinomios
-- ---------------------------------------------------------------------

-- | (productoMM m1 m2) es el producto de los monomios m1 y m2. Por
-- ejemplo,
--
-- >>> productoMM (M ["x","y"]) (M ["y","z"])
-- x*y*z
productoMM :: Monomio -> Monomio -> Monomio
productoMM (M x) (M y) = M (sort (x `union` y))

-- | (productoMP m p) es el producto del monomio m por el polinomio
-- p. Por ejemplo,
--
-- >>> productoMP (M ["x","y"]) (P [M ["a"], M ["y","z"]])
-- a*x*y+x*y*z
productoMP :: Monomio -> Polinomio -> Polinomio
productoMP m1 (P [])     = P []
productoMP m1 (P (m:ms)) = (P [productoMM m1 m]) + (productoMP m1 (P ms))

-- | (producto p1 p2) es el producto de los polinomios p1 y p2. Por
-- ejemplo,
--
-- >>> producto (P [M ["x","y"], M ["z"]]) (P [M ["a"], M ["y","z"]])
-- a*x*y+a*z+x*y*z+y*z
-- >>> producto (P [M ["x","y"], M ["z"]]) (P [M ["x"], M ["y","z"]])
-- x*y+x*y*z+x*z+y*z
-- >>> producto (P [M ["x"], M ["y"]]) (P [M ["x"], M ["y"]]) 
-- x+y
producto :: Polinomio -> Polinomio -> Polinomio
producto (P []) _     = P []
producto (P (m:ms)) q = (productoMP m q) + (producto (P ms) q)

-- | Comprueba que el producto de polinomios está bien definido.
--
-- >>> quickCheck prop_prod_bien_definido
-- +++ OK, passed 100 tests.
prop_prod_bien_definido :: Polinomio -> Polinomio -> Bool
prop_prod_bien_definido p q = esPolinomio (p*q)

-- | Comprueba que el producto de polinomios es conmutativo 
--
-- >>> quickCheck prop_prod_conmutativa
-- +++ OK, passed 100 tests.
prop_prod_conmutativa :: Polinomio -> Polinomio -> Bool
prop_prod_conmutativa p q = p*q == q*p

-- | Comprueba que el producto de polinomios es distributivo respecto de
-- la suma.
--
-- >>> quickCheck prop_distributiva
-- +++ OK, passed 100 tests.
prop_distributiva :: Polinomio -> Polinomio -> Polinomio -> Bool
prop_distributiva p q r = p*(q+r) == (p*q)+(p*r)

-- ---------------------------------------------------------------------
-- ** Derivada de polinomios
-- ---------------------------------------------------------------------

-- | (deriv p x) es la derivada del polinomio p respecto de la variable
-- x; es decir, la lista de monomios de p que contienen la variable x,
-- eliminándola. Por ejemplo,
--
-- >>> deriv (P [M ["u"],M ["x"],M ["x","y"],M ["x","z"]]) "x"
-- 1+y+z
deriv :: Polinomio -> Variable -> Polinomio
deriv (P ms) x = P [M (delete x m) | (M m) <- ms, elem x m]

-- | Comprueba que la derivada está bien definida.
--
-- >>> quickCheck prop_deriv_bien_definida
-- +++ OK, passed 100 tests.
prop_deriv_bien_definida :: Polinomio -> Variable -> Bool
prop_deriv_bien_definida p x = esPolinomio (deriv p x)

-- | Comprueba que la segunda derivada es nula.
--
-- >>> quickCheck prop_deriv_deriv
-- +++ OK, passed 100 tests.
prop_deriv_deriv :: Polinomio -> Variable -> Bool
prop_deriv_deriv p x = deriv (deriv p x) x == cero

-- | Comprueba que la derivada de la suma es la suma de las derivadas. 
--
-- >>> quickCheck prop_deriv_suma
-- +++ OK, passed 100 tests.
prop_deriv_suma :: Polinomio -> Polinomio -> Variable -> Bool
prop_deriv_suma p q x = deriv (p+q) x == (deriv p x) + (deriv q x) 

-- | Comprueba que la regla de la derivada del producto
--
-- >>> quickCheck prop_deriv_prod
-- +++ OK, passed 100 tests.
prop_deriv_prod :: Polinomio -> Polinomio -> Variable -> Bool
prop_deriv_prod p q x = deriv (p*q) x == (deriv p x)*q + p*(deriv q x) 

-- ---------------------------------------------------------------------
-- * Transformaciones entre fórmulas y polinomios
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- ** Transformación de proposiciones en polinomios
-- ---------------------------------------------------------------------

-- | (tr f) es el polinomio correspondiente a la fórmula f. Por ejemplo,
--
-- >>> tr (p ∧ (q ∨ r))
-- p*q+p*q*r+p*r
-- >>> tr (p → p ∨ q)
-- 1
-- >>> tr ((p → q) ∨ (q → p))
-- 1
-- >>> tr ((p → q) ∨ (q → r))
-- 1
-- >>> tr ((p → q) ∨ (r → q))
-- 1+p*q*r+p*r
tr :: FProp -> Polinomio
tr T          = uno
tr F          = cero
tr (Atom a)   = P [M [a]]
tr (Neg a)    = uno + tr a
tr (Conj a b) = tr a * tr b
tr (Disj a b) = tr a + tr b + tr a * tr b
tr (Impl a b) = uno + tr a + tr a * tr b
tr (Equi a b) = uno + tr a + tr b

-- | Comprueba que, para toda fórmula f, (tr f) es un polinomio.
--
-- >>> quickCheck pro_tr_bien_definida
-- +++ OK, passed 100 tests.
pro_tr_bien_definida :: FProp -> Bool
pro_tr_bien_definida f = esPolinomio (tr f)

-- ---------------------------------------------------------------------
-- ** Transformación de polinomios en proposiciones
-- ---------------------------------------------------------------------

-- | (theta2 m) es la fórmula correspondiente al polinomio p según las
-- siguientes reglas:
-- 
-- * theta 0     = F
-- * theta (a+b) = no ((theta a) ↔ (theta b))
-- 
-- Por ejemplo,
--
-- >>> theta (P [mUno])
-- ⊤
-- >>> theta (P [mUno, M ["p"]])
-- ¬(⊤ ↔ p)
-- >>> theta (P [mUno, M ["p"], M ["p","q"]])
-- ¬(⊤ ↔ ¬(p ↔ (p ∧ q)))
-- >>> theta (P [mUno, M ["p"], M ["p","q"],M["p","q","r"]])
-- ¬(⊤ ↔ ¬(p ↔ ¬((p ∧ q) ↔ (p ∧ (q ∧ r)))))
-- >>> theta (P [mUno, M ["p"], M ["p","q"],M["p","q","r"],M["r"]])
-- ¬(⊤ ↔ ¬(p ↔ ¬((p ∧ q) ↔ ¬((p ∧ (q ∧ r)) ↔ r))))
theta :: Polinomio -> FProp
theta (P ms) = thetaAux ms
  where thetaAux :: [Monomio] -> FProp
        thetaAux []     = F
        thetaAux [m]    = theta2 m
        thetaAux (m:ms) = no ((theta2 m) ↔ (theta (P ms)))

-- | (theta2 m) es la fórmula correspondiente al monomio m según las
-- siguientes reglas:
-- 
-- * theta2 1     = T
-- * theta2 (x_i) = p_i
-- * theta2 (a*b) = (theta2 a) ∧ (theta2 b)
-- 
-- Por ejemplo,
--
-- >>> theta2 (M ["p","q","r"])
-- (p ∧ (q ∧ r))
theta2 :: Monomio -> FProp
theta2 (M vs) = theta2Aux vs
  where theta2Aux :: [SimboloProposicional] -> FProp
        theta2Aux []     = T
        theta2Aux [v]    = Atom v
        theta2Aux (v:vs) = Conj (Atom v) (theta2Aux vs)

-- | Comprueba que para cualquier fórmula f, (theta (tr f)) es
-- equivalente a f.
--
-- >>> quickCheck prop_theta_tr
-- +++ OK, passed 100 tests.
prop_theta_tr :: FProp -> Bool
prop_theta_tr f = equivalentes (theta (tr f)) f

-- | Comprueba que, para cualquier polinomio p, tr (theta p) es igual a
-- p. 
--
-- >>> quickCheck prop_tr_theta
-- +++ OK, passed 100 tests.
prop_tr_theta :: Polinomio -> Bool
prop_tr_theta p = tr (theta p) == p

-- ---------------------------------------------------------------------
-- * La regla de la independencia
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- ** Derivación de fórmulas proposicionales
-- ---------------------------------------------------------------------

-- | (derivP f v) es la derivada de la fórmula proposicional f respecto
-- de la variable v. Por ejemplo,
--
-- >>> derivP (p ∧ q → r) "p"
-- ¬(q ↔ (q ∧ r))
-- >>> derivP (p ∧ q → r) "q"
-- ¬(p ↔ (p ∧ r))
-- >>> derivP (p ∧ q → r) "r"
-- (p ∧ q)
-- >>> derivP (p ∧ q → p ∨ q) "p"
-- ⊥
derivP :: FProp -> SimboloProposicional -> FProp
derivP f v = theta (deriv (tr f) v)

-- | (sustituir f v g) es la fórmula obtenida sustituyendo en la fórmula f
-- la variable v por la fórmula g. Por ejemplo,
--
-- >>> sustituir (p → q ∨ r) "q" (p ∧ q)
-- (p → ((p ∧ q) ∨ r))
sustituir :: FProp -> SimboloProposicional -> FProp -> FProp
sustituir T  _ _           = T
sustituir F  _ _           = F
sustituir (Atom x) v g 
  | x == v                 = g
  | otherwise              = (Atom x)
sustituir (Neg f) v g      = Neg (sustituir f v g)
sustituir (Disj f1 f2) v g = Disj (sustituir f1 v g) (sustituir f2 v g)
sustituir (Conj f1 f2) v g = Conj (sustituir f1 v g) (sustituir f2 v g)
sustituir (Impl f1 f2) v g = Impl (sustituir f1 v g) (sustituir f2 v g)
sustituir (Equi f1 f2) v g = Equi (sustituir f1 v g) (sustituir f2 v g)

-- | (variablesProp f) es la lista de las variables proposicionales de
-- la fórmula f. Por ejemplo,
--
-- >>> variablesProp (p → q ∨ p)
-- ["p","q"]
variablesProp :: FProp -> [SimboloProposicional]
variablesProp f = [v | (Atom v) <- simbolosPropForm f]

-- | Comprueba que, para toda fórmula f y toda variable x de f, la
-- derivada de f respecto de x es equivalente a la fórmula ¬(f[x/¬x] ↔ f)
--
-- >>> quickCheck prop_derivP_sustituir
-- +++ OK, passed 100 tests.
prop_derivP_sustituir :: FProp -> Bool
prop_derivP_sustituir f = 
  and [equivalentes (derivP f x) 
                    (no (sustituir f x (no (Atom x))) ↔ f)
      | x <- variablesProp f]

-- ---------------------------------------------------------------------
-- ** La regla de independencia (regla delta)
-- ---------------------------------------------------------------------

-- | (indep p x) es el polinomio formado por los monomios de que no
-- contienen la variable x. Por ejemplo,
--
-- >>> indep (P[M["x","y"],M["y","u"],M ["z"]]) "x"
-- y*u+z
indep :: Polinomio -> Variable -> Polinomio
indep (P ms) x = P [M m | (M m) <- ms, notElem x m]

-- | (delta a1 a2 v) es el polinomio obtenido aplicando la regla delta
-- (o de independencia) a los polinomios a1 y a2 respecto de la variable
-- v; es decir, el polinomio 1 + (1+a1*a2)*(1+a1*c2+a2*c1+c1*c2) donde
-- ci es la derivada de ai respecto de v (para i = 1, 2). Por ejemplo,
--
-- >>> delta (P[M["x","y"],M["y","z"]]) (P[M["u","x"],M["y","z"]]) "x"
-- u*y+u*y*z+y*z
delta :: Polinomio -> Polinomio -> Variable -> Polinomio
delta a1 a2 v = uno + ((uno+a1*a2)*(uno+a1*c2+a2*c1+c1*c2))
  where
    c1 = deriv a1 v
    c2 = deriv a2 v

-- | (delta' a1 a2 v) es el polinomio 1 + (1+b1*b2)*(1+(b1+c1)*(b2+c2))
-- donde ci es la derivada de ai respecto de v y bi es es el polinomio
-- formado por los monomios de ai que no contienen la variable x  (para
-- i = 1, 2). Por ejemplo, 
--
-- >>> delta' (P[M["x","y"],M["y","z"]]) (P[M["u","x"],M["y","z"]]) "x"
-- u*y+u*y*z+y*z
delta' :: Polinomio -> Polinomio -> Variable -> Polinomio
delta' a1 a2 v = uno + (uno+b1*b2)*(uno+(b1+c1)*(b2+c2))
    where
      c1 = deriv a1 v
      c2 = deriv a2 v
      b1 = indep a1 v
      b2 = indep a2 v

-- | Comprueba que las funciones delta y delta' son equivalentes.
--
-- >>> quickCheck prop_equiv_delta_delta'
-- +++ OK, passed 100 tests.
prop_equiv_delta_delta' :: Polinomio -> Polinomio -> Bool
prop_equiv_delta_delta' a1 a2 =
  and [delta a1 a2 v == delta' a1 a2 v | v <- variablesPol (a1+a2)]

-- | (variablesMon m) es la lista de las variables del monomio m. Por
-- ejemplo,
-- 
-- >>> variablesMon (M ["x","z"])
-- ["x","z"]
variablesMon :: Monomio -> [Variable]
variablesMon (M vs) = vs

-- | (variablesPol p) es la lista de las variables del polinomio p. Por
-- ejemplo, 
-- 
-- >>> variablesPol (P[M["x","z"],M["y","z"]])
-- ["x","z","y"]
variablesPol :: Polinomio -> [Variable]
variablesPol (P [])     = []
variablesPol (P (m:ms)) = (variablesMon m) `union` (variablesPol (P ms))


-- | (deltaP f1 f2 v) es la f§ormula obtenida aplicando la regla delta
-- (o de independencia) a las fórmulas f1 y f2 respecto de la variable
-- v. Por ejemplo,
--
-- >>> deltaP (r → p ∨ q) (q → p ∧ q) "q"
-- ¬(⊤ ↔ ¬((p ∧ r) ↔ r))
deltaP :: FProp -> FProp -> SimboloProposicional -> FProp
deltaP f1 f2 v = theta (delta (tr f1) (tr f2) v) 

-- ---------------------------------------------------------------------
-- ** Adecuación y completitud de la regla de independencia
-- ---------------------------------------------------------------------

prop_adecuacion_deltaP :: FProp -> FProp -> Bool
prop_adecuacion_deltaP f1 f2 = 
    and [esConsecuencia [f1, f2] (deltaP f1 f2 x) |
         x <- variablesProp (f1 ∧ f2)]

-- (pares xs) es la lista de los pares de elementos xs xon el primero
-- menor o igual que el segundo. Por ejemplo,
--    *Polinomios> pares [1..4]
--    [(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]
pares :: [a] -> [(a,a)]
pares []  = []
pares [x] = [(x,x)]
pares (x:xs) = [(x,y) | y <- (x:xs)] ++ (pares xs)

-- (derivadas ps x) es la lista de los polinomios obtenidos aplicando
-- la regla delta a dos polinomios de ps respecto de la variable x.
derivadas :: [Polinomio] -> Variable -> [Polinomio]
derivadas ps x = delete uno (nub [delta p1 p2 x | (p1,p2) <- pares ps])

-- (derivadasP fs x) es la lista de las proposiciones obtenidas aplicando
-- la regla deltaP a dos fórmulas de fs respecto de la variable x.
derivadasP :: [FProp] -> SimboloProposicional -> [FProp]
derivadasP fs x = delete T (nub [deltaP f1 f2 x | (f1,f2) <- pares fs])

-- (deltaRefutable fps) se verifica si ps es refutable mediante la regla
-- delta. 
deltaRefutable :: [Polinomio] -> Bool
deltaRefutable [] = False
deltaRefutable ps =
    (elem cero ps) || (deltaRefutable (derivadas ps (eligeVariable ps)))
    where eligeVariable ps = head (concat [variablesPol p | p <- ps])

-- Definición equivalente
deltaRefutableP' :: [FProp] -> Bool
deltaRefutableP' [] = False
deltaRefutableP' fs =
    (elem F fs) || (deltaRefutableP' (derivadasP fs (eligeVariable fs)))
    where eligeVariable fs = head (concat [variablesProp f | f <- fs])

-- Las dos definiciones de deltaRefutableP son equivalentes.
prop_def_alt_deltaRefutableP fs =
    deltaRefutableP fs == deltaRefutableP' fs

prop_adecuacion_completitud_deltaP :: [FProp] -> Bool
prop_adecuacion_completitud_deltaP fs = 
    esInconsistente fs == deltaRefutableP fs

-- (deltaDemostrable fs g) se verifica si g es demostrable a partir de
-- fs usando la regla delta. Por ejemplo,
--    *Polinomios> deltaDemostrable [p → q, q → r] (p → r)
--    True
deltaDemostrable :: [FProp] -> FProp -> Bool
deltaDemostrable fs g = deltaRefutableP ((no g):fs)

prop_adecuacion_completitud_delta_2 :: [FProp] -> FProp -> Bool
prop_adecuacion_completitud_delta_2 fs g =
    esConsecuencia fs g == deltaDemostrable fs g

deltaTeorema :: FProp -> Bool
deltaTeorema f = deltaRefutableP [no f]

prop_adecuacion_completitud_delta_3 :: FProp -> Bool
prop_adecuacion_completitud_delta_3 f =
    esValida f == deltaTeorema f

-- (deltaRefutableP fs) se verifica si fs es refutable mediante la regla
-- delta. 
deltaRefutableP :: [FProp] -> Bool
deltaRefutableP fs = deltaRefutable [tr f | f <- fs]

-- ---------------------------------------------------------------------
-- ** Delta refutabilidad usando soporte
-- ---------------------------------------------------------------------

deltaRefutableSop :: [Polinomio] -> Bool
deltaRefutableSop ps =
    deltaRefutableSop' ps []

deltaRefutableSop' :: [Polinomio] -> [Polinomio] -> Bool
deltaRefutableSop' soporte usables
    | null soporte    = False
    | elem cero soporte = True
    | otherwise       =
        deltaRefutableSop' soporte' usables'
        where actual   = head soporte
              usables' = union [actual] usables
              soporte' = union (tail soporte)
                               [p 
                                | p <- derivadasPolConjunto
                                       actual 
                                       usables'
                                , p /= uno
                                , notElem p soporte
                                , notElem p usables']

derivadasPolConjunto :: Polinomio -> [Polinomio] -> [Polinomio]
derivadasPolConjunto p qs = 
    nub (concat [derivadasPolPol p q | q <- qs])

derivadasPolPol :: Polinomio -> Polinomio -> [Polinomio]
derivadasPolPol p q =
    nub [delta p q x | x <- variablesPol (p+q)]

-- Las definición con soporte es equivalente son equivalentes.
prop_deltaRefutableSop ps =
    deltaRefutable ps == deltaRefutableSop ps

-- (deltaRefutablePSop fs) se verifica si fs es refutable mediante la regla
-- delta. 
deltaRefutablePSop :: [FProp] -> Bool
deltaRefutablePSop fs = deltaRefutableSop [tr f | f <- fs]

prop_adecuacion_completitud_deltaPSop :: [FProp] -> Bool
prop_adecuacion_completitud_deltaPSop fs = 
    esInconsistente fs == deltaRefutableP fs

-- ---------------------------------------------------------------------
-- ** Problema del palomar
-- ---------------------------------------------------------------------

palomar :: [FProp]
palomar = [-- La paloma 1 está en alguna hueco:
           p1h1 ∨ (p1h2 ∨ p1h3),
                  
           -- La paloma 2 está en alguna hueco:
           p2h1 ∨ (p2h2 ∨ p2h3),
           
           -- La paloma 3 está en alguna hueco:
           p3h1 ∨ (p3h2 ∨ p3h3),
           
           -- La paloma 4 está en alguna hueco:
           p4h1 ∨ (p4h2 ∨ p4h3),

           -- No hay dos palomas en la hueco 5:
           (no p1h1) ∨ (no p2h1),
           (no p1h1) ∨ (no p3h1),
           (no p1h1) ∨ (no p4h1),
           (no p2h1) ∨ (no p3h1),
           (no p2h1) ∨ (no p4h1),
           (no p3h1) ∨ (no p4h1),
           
           -- No hay dos palomas en la hueco 6:
           (no p1h2) ∨ (no p2h2),
           (no p1h2) ∨ (no p3h2),
           (no p1h2) ∨ (no p4h2),
           (no p2h2) ∨ (no p3h2),
           (no p2h2) ∨ (no p4h2),
           (no p3h2) ∨ (no p4h2),
           
           -- No hay dos palomas en la hueco 7:
           (no p1h3) ∨ (no p2h3),
           (no p1h3) ∨ (no p3h3),
           (no p1h3) ∨ (no p4h3),
           (no p2h3) ∨ (no p3h3),
           (no p2h3) ∨ (no p4h3),
           (no p3h3) ∨ (no p4h3)]
    where p1h1 = Atom "p1h1"
          p1h2 = Atom "p1h2"
          p1h3 = Atom "p1h3"
          p2h1 = Atom "p2h1"
          p2h2 = Atom "p2h2"
          p2h3 = Atom "p2h3"
          p3h1 = Atom "p3h1"
          p3h2 = Atom "p3h2"
          p3h3 = Atom "p3h3"
          p4h1 = Atom "p4h1"
          p4h2 = Atom "p4h2"
          p4h3 = Atom "p4h3"
          
-- ---------------------------------------------------------------------
-- * Bibliografía
-- ---------------------------------------------------------------------

{-|
$bib

* Wikipedia: <http://bit.ly/2tYsY9A Zhegalkin polynomial>
* G.A. Aranda, J. Borrego y  M.M. Fernández (2009)
  <http://bit.ly/2tYdN0d Conservative retractions of propositional logic
  theories by means of boolean derivatives. Theoretical foundations.> 
* M. Brickenstein y A. Dreyer:
  <http://bit.ly/2tuf4sA PolyBoRi: A Gröbner basis framework for Boolean
  polynomials.>
* M. Clegg, J. Edmonds y R. Impagliazzo (1996):
  <http://bit.ly/2tY7wl5 Using the Groebner basis algorithm to find
  proofs of unsatisfiability.> 
$bib
-}
