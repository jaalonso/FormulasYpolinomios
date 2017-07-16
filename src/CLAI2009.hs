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
    show (Atom p)   = p
    show (Neg p)    = "¬" ++ show p
    show (Conj p q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
    show (Disj p q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
    show (Impl p q) = "(" ++ show p ++ " → " ++ show q ++ ")"
    show (Equi p q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"

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

-- | 'f ∨ g' es la disyunción de f y g
(∨) :: FProp -> FProp -> FProp
(∨)   = Disj
infixr 5 ∨

-- | f ∧ g es la conjunción de f y g
(∧) :: FProp -> FProp -> FProp
(∧)   = Conj
infixr 4 ∧

-- | f → g es la implicación de f a g
(→) :: FProp -> FProp -> FProp
(→)  = Impl
infixr 3 →

-- | f ↔ g es la equivalencia entre f y g
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

-- | Las interpretaciones como listas de fórmulas atómicas.
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

-- | (subconjuntos x) es la lista de los subconjuntos de x. Por ejemplo,
-- 
-- >>> subconjuntos "abc"
-- ["abc","ab","ac","a","bc","b","c",""]
subconjuntos :: [a] -> [[a]]
subconjuntos []     = [[]]
subconjuntos (x:xs) = [x:ys | ys <- xss] ++ xss
  where xss = subconjuntos xs

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

-- (interpretacionesForm f) es la lista de todas las interpretaciones de
-- la fórmula f. Por ejemplo,  
--    interpretacionesForm (p ∧ q → p)  ==>  [[p,q],[p],[q],[]]
interpretacionesForm :: FProp -> [Interpretacion]
interpretacionesForm f = subconjuntos (simbolosPropForm f)

-- (esModeloFormula i f) se verifica si la interpretación i es un modelo
-- de la fórmula f. Por ejemplo, 
--    esModeloFormula [r]   ((p ∨ q) ∧ ((no q) ∨ r))    ==>  False
--    esModeloFormula [p,r] ((p ∨ q) ∧ ((no q) ∨ r))    ==>  True
esModeloFormula :: Interpretacion -> FProp -> Bool
esModeloFormula i f = significado f i

-- (modelosFormula f) es la lista de todas las interpretaciones de la
-- fórmula f que son modelo de F. Por ejemplo, 
--    modelosFormula ((p ∨ q) ∧ ((no q) ∨ r)) 
--    ==> [[p,q,r],[p,r],[p],[q,r]]
modelosFormula :: FProp -> [Interpretacion]
modelosFormula f =
    [i | i <- interpretacionesForm f,
         esModeloFormula i f]

-- ---------------------------------------------------------------------
-- ** Fórmulas válidas, satisfacibles e insatisfacibles
-- ---------------------------------------------------------------------

-- (esValida f) se verifica si la fórmula f es válida. Por ejemplo,
--    esValida (p → p)                 ==>  True
--    esValida (p → q)                 ==>  False
--    esValida ((p → q) ∨ (q → p))  ==>  True
esValida :: FProp -> Bool
esValida f = 
    modelosFormula f == interpretacionesForm f

prop_esValida f =
   esValida f == esConsecuencia [] f

-- (esInsatisfacible f) se verifica si la fórmula f es insatisfacible. 
-- Por ejemplo, 
--    esInsatisfacible (p ∧ (no p))             ==>  True
--    esInsatisfacible ((p → q) ∧ (q → r))  ==>  False
esInsatisfacible :: FProp -> Bool
esInsatisfacible f =
    modelosFormula f == []

-- (esSatisfacible f) se verifica si f es satisfacible. Por ejemplo, 
--    esSatisfacible (p ∧ (no p))             ==>  False
--    esSatisfacible ((p → q) ∧ (q → r))  ==>  True
esSatisfacible :: FProp -> Bool
esSatisfacible f =
    modelosFormula f /= []

-- ---------------------------------------------------------------------
-- ** Interpretaciones de un conjunto de fórmulas
-- ---------------------------------------------------------------------

-- (unionGeneral x) es la unión de los conjuntos de la lista de
-- conjuntos x. Por ejemplo, 
--    unionGeneral []                 ==>  []
--    unionGeneral [[1]]              ==>  [1]
--    unionGeneral [[1],[1,2],[2,3]]  ==>  [1,2,3]
unionGeneral :: Eq a => [[a]] -> [a]
unionGeneral []     = []
unionGeneral (x:xs) = x `union` unionGeneral xs 

-- (simbolosPropConj s) es el conjunto de los símbolos proposiciones de 
-- s. Por ejemplo,
--    simbolosPropConj [p ∧ q → r, p → s]  ==>  [p,q,r,s]
simbolosPropConj :: [FProp] -> [FProp]
simbolosPropConj s
    = unionGeneral [simbolosPropForm f | f <- s]

-- (interpretacionesConjunto s) es la lista de las interpretaciones de 
-- s. Por ejemplo,
--    interpretacionesConjunto [p → q, q → r]
--    ==> [[p,q,r],[p,q],[p,r],[p],[q,r],[q],[r],[]]
interpretacionesConjunto :: [FProp] -> [Interpretacion]
interpretacionesConjunto s =
    subconjuntos (simbolosPropConj s)

-- ---------------------------------------------------------------------
-- ** Modelos de conjuntos de fórmulas
-- ---------------------------------------------------------------------

-- (esModeloConjunto i s) se verifica si i es modelo de s. Por ejemplo, 
--    esModeloConjunto [p,r] [(p ∨ q) ∧ ((no q) ∨ r), q → r]
--    ==> True
--    esModeloConjunto [p,r] [(p ∨ q) ∧ ((no q) ∨ r), r → q]
--    ==> False
esModeloConjunto :: Interpretacion -> [FProp] -> Bool
esModeloConjunto i s =
    and [esModeloFormula i f | f <- s]

-- (modelosConjunto s) es la lista de modelos del conjunto s. 
-- Por ejemplo,
--    modelosConjunto [(p ∨ q) ∧ ((no q) ∨ r), q → r]
--    ==> [[p,q,r],[p,r],[p],[q,r]]
--    modelosConjunto [(p ∨ q) ∧ ((no q) ∨ r), r → q]
--    ==> [[p,q,r],[p],[q,r]]
modelosConjunto :: [FProp] -> [Interpretacion]
modelosConjunto s =
    [i | i <- interpretacionesConjunto s,
         esModeloConjunto i s]

-- ---------------------------------------------------------------------
-- ** Conjuntos consistentes e inconsistentes de fórmulas
-- ---------------------------------------------------------------------

-- (esConsistente s) se verifica si s es consistente. Por ejemplo, 
--    esConsistente [(p ∨ q) ∧ ((no q) ∨ r), p → r]        
--    ==> True
--    esConsistente [(p ∨ q) ∧ ((no q) ∨ r), p → r, no r]  
--    ==> False
esConsistente :: [FProp] -> Bool
esConsistente s =
    modelosConjunto s /= []

-- (esInconsistente s) se verifica si s es inconsistente. Por ejemplo, 
--    esInconsistente [(p ∨ q) ∧ ((no q) ∨ r), p → r]        
--    ==> False
--    esInconsistente [(p ∨ q) ∧ ((no q) ∨ r), p → r, no r]  
--    ==> True
esInconsistente :: [FProp] -> Bool
esInconsistente s =
    modelosConjunto s == []

-- ---------------------------------------------------------------------
-- ** Consecuencia lógica
-- ---------------------------------------------------------------------

-- (esConsecuencia s f) se verifica si f es consecuencia de s. Por 
-- ejemplo,
--    esConsecuencia [p → q, q → r] (p → r)  ==>  True
--    esConsecuencia [p] (p ∧ q)                  ==>  False
esConsecuencia :: [FProp] -> FProp -> Bool
esConsecuencia s f =
    null [i | i <- interpretacionesConjunto (f:s),
              esModeloConjunto i s,
              not (esModeloFormula i f)]

prop_esConsecuencia s f =
   esConsecuencia s f == esInconsistente (Neg f:s)

-- ---------------------------------------------------------------------
-- ** Equivalencia de fórmulas
-- ---------------------------------------------------------------------

-- (equivalentes f g) se verifica si las fórmulas f y g son equivalentes
equivalentes :: FProp -> FProp -> Bool
equivalentes f g = esValida (f ↔ g)

-- =====================================================================
-- * Polinomios
-- =====================================================================

-- ---------------------------------------------------------------------
-- ** Variables
-- ---------------------------------------------------------------------

-- caracteres es un generador de caracteres de letras minúsculas. Por ejemplo,
--    *Main> sample caracteres
--    'x'
--    'n'
--    'r'
caracteres :: Gen Char
caracteres = chr `fmap` choose (97,122)

-- Las variables se representan por cadenas.
type Variable = String

-- variables es un generador de variables de longitud 1 ó 2. Por ejemplo,
--    *Main> sample variables
--    "h"
--    "yi"
--    "m"
variables :: Gen String
variables = do k <- choose (1,2)
               vectorOf k caracteres

-- variables' es un generador de variables de longitud aleatoria, pero
-- no cero. Por ejemplo, 
--    *Main> sample variables'
--    "o"
--    "rte"
--    "tmzeu"
variables' :: Gen String
variables' = listOf1 caracteres

-- ---------------------------------------------------------------------
-- ** Monomios
-- ---------------------------------------------------------------------

-- Los monomios son productos de variables distintas y se representan por
-- listas ordenadas de variables distintas. 
data Monomio = M [Variable] 
               deriving (Eq, Ord)

-- El monomio correspondiente a la lista vacía es el 1 (elemento neutro
-- del producto).
mUno :: Monomio
mUno = M []

-- La condición de que las variables sean distintas y ordenadas no se
-- recoge en la definición del tipo de dato. Por ello se define el
-- siguiente reconocedor de monomios.
esMonomio :: Monomio -> Bool
esMonomio (M vs) = vs == sort (nub vs)

-- Los monomios se escribe incercalando el * entre sus variables. Por
-- ejemplo,
--    *Main> M ["xy","z","u"] 
--    xy*z*u
instance Show Monomio where
    show (M [])     = "1"
    show (M [v])    = v
    show (M (v:vs)) = concat [v, "*", show (M vs)]

-- (monomiosN n) es un generador de monomios con el número de variables
-- entre 0 y n. Por ejemplo,
--    *Main> sample (monomiosN 3)
--    1
--    s
--    e*t
--    hx*w*xn
--    *Main> sample (monomiosN 10)
--    at*b*dy*fq*gv*mx*y*z
--    a*cm*d*f*h*wf*z
--    b*dw*wx*x*y*z
monomiosN :: Int -> Gen Monomio
monomiosN n = do k <- choose (0,n)
                 vs <- vectorOf k variables
                 return (M (sort (nub vs)))

-- monomios es un generador de monomios con el número de variables
-- entre 0 y 3. Por ejemplo,
--    *Main> sample monomios
--    nd*q
--    e
--    1
monomios :: Gen Monomio
monomios = monomiosN 3

-- monomios' es un generador de monomios con un número aleatorio de
-- variables. Por ejemplo, 
--    *Main> sample monomios'
--    1
--    kl*o*u
--    bm*d*k*mk
monomios' :: Gen Monomio
monomios' = do xs <- listOf variables
               return (M (sort (nub xs)))

-- Nota. En lo que sigue usa el generador monomio.

-- Comprobación que el generador de monomios genera monomios.
prop_MonomiosGeneraMonomios :: Monomio -> Bool
prop_MonomiosGeneraMonomios m = esMonomio m

-- Los monomios son arbitrarios.
instance Arbitrary Monomio where
    arbitrary = monomios

-- ---------------------------------------------------------------------
-- ** Polinomios
-- ---------------------------------------------------------------------

-- Los polinomios son sumas de monomios distintos y ordenados y se
-- representan por listas ordenadas de monomios distintos, 
data Polinomio = P [Monomio]
                 deriving (Eq, Ord)

-- El polinomio correspondiente a la lista vacía es el 0 (elemento
-- neutro de la suma).
cero :: Polinomio
cero = P []

-- El polinomio 1 es el polinomio cuyo único elemento es el monomio uno.
uno  :: Polinomio
uno = P [mUno]

-- La condición de que los monomios sean distintos y ordenados no se
-- recoge en la definición del tipo de dato. Por ello se define el
-- siguiente reconocedor de polinomios.
esPolinomio :: Polinomio -> Bool
esPolinomio (P ms) = ms == sort (nub ms)

-- Los polinomios se escribe incercalando el + entre sus monomios. Por
-- ejemplo,
--    *Main> P [M ["xy","z","u"], M ["p","q"]] 
--    xy*z*u+p*q
instance Show Polinomio where
    show (P [])     = "0"
    show (P [m])    = show m
    show (P (m:ms)) = concat [show m, "+", show (P ms)]

-- (polinomiosN n) es un generador de polinomios con el número de monomios
-- entre 0 y n. Por ejemplo,
--    *Main> sample (polinomiosN 3)
--    0
--    pp*sa
--    gn*nf*zg
--    *Main> sample (polinomiosN 10)
--    1+b*j+gw*w*zm+j*ox+l*q*qz+ly*p*r+m+q*zy
--    iz
--    1+d+dy+jd*l+lr+w
polinomiosN :: Int -> Gen Polinomio
polinomiosN n = do k <- choose (0,n)
                   ms <- vectorOf k monomios
                   return (P (sort (nub ms)))

-- polinomios es un generador de polinomios con el número de monomios
-- entre 0 y 3. Por ejemplo,
--    *Main> sample monomios
--    nd*q
--    e
--    1
polinomios :: Gen Polinomio
polinomios = polinomiosN 3

-- polinomios' es un generador de polinomios con un número aleatorio de
-- monomios. Por ejemplo, 
--    *Main> sample polinomios'
--    0
--    1
--    f*m*on*tr*ue*x
--    ct*d*ds*gy*ps*s*y
polinomios' :: Gen Polinomio
polinomios' = do xs <- listOf1 monomios
                 return (P (sort (nub xs)))

-- Comprobación que el generador de polinomios genera polinomios.
prop_PolinomiosGeneraPolinomios :: Polinomio -> Bool
prop_PolinomiosGeneraPolinomios p = esPolinomio p

-- Los polinomios son arbitrarios.
instance Arbitrary Polinomio where
    arbitrary = polinomios

-- Nota. Para facilitar la escritura, se hace Polinomio una instancia de
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

-- (suma p q) es la suma de los polinomios p y q.
suma :: Polinomio -> Polinomio -> Polinomio
suma (P []) (P q) = (P q)
suma (P p)  (P q) = P (sumaAux p q)

sumaAux :: [Monomio] -> [Monomio] -> [Monomio]
sumaAux [] y      = y
sumaAux (c:r) y
    | (elem c y) = sumaAux r (delete c y)
    | otherwise  = insert c (sumaAux r y)

prop_suma_bien_definida :: Polinomio -> Polinomio -> Bool
prop_suma_bien_definida p q = esPolinomio (p+q)

prop_suma_conmutativa :: Polinomio -> Polinomio -> Bool
prop_suma_conmutativa p q = p+q == q+p

prop_suma_asociativa :: Polinomio -> Polinomio -> Polinomio -> Bool
prop_suma_asociativa p q r = p+(q+r) == (p+q)+r

prop_suma_neutro :: Polinomio -> Bool
prop_suma_neutro p = p + cero == p

prop_suma_simetrico :: Polinomio -> Bool
prop_suma_simetrico p = p+p == cero

prop_distributiva :: Polinomio -> Polinomio -> Polinomio -> Bool
prop_distributiva p q r = p*(q+r) == (p*q)+(p*r)

-- ---------------------------------------------------------------------
-- ** Productos de polinomios
-- ---------------------------------------------------------------------

productoMM :: Monomio -> Monomio -> Monomio
productoMM (M x) (M y) = M (sort (x `union` y))

productoMP :: Monomio -> Polinomio -> Polinomio
productoMP m1 (P [])     = P []
productoMP m1 (P (m:ms)) = (P [productoMM m1 m]) + (productoMP m1 (P ms))

producto :: Polinomio -> Polinomio -> Polinomio
producto (P []) _     = P []
producto (P (m:ms)) q = (productoMP m q) + (producto (P ms) q)

prop_prod_bien_definido :: Polinomio -> Polinomio -> Bool
prop_prod_bien_definido p q = esPolinomio (p*q)

prop_prod_conmutativa :: Polinomio -> Polinomio -> Bool
prop_prod_conmutativa p q = p*q == q*p

-- ---------------------------------------------------------------------
-- ** Derivada de polinomios
-- ---------------------------------------------------------------------

-- (deriv p x) es la derivada del polinomio p respecto de la variable
-- x; es decir, la lista de monomios de p que contienen la variable x,
-- eliminándola. Por ejemplo,
--    *Main> deriv (P [M ["u"],M ["x"],M ["x","y"],M ["x","z"]]) "x"
--    1+y+z
deriv :: Polinomio -> Variable -> Polinomio
deriv (P ms) x = P [M (delete x m) | (M m) <- ms, elem x m]

prop_deriv_bien_definida :: Polinomio -> Variable -> Bool
prop_deriv_bien_definida p x = esPolinomio (deriv p x)

prop_deriv_deriv :: Polinomio -> Variable -> Bool
prop_deriv_deriv p x = deriv (deriv p x) x == cero

prop_deriv_suma :: Polinomio -> Polinomio -> Variable -> Bool
prop_deriv_suma p q x = deriv (p+q) x == (deriv p x) + (deriv q x) 

prop_deriv_prod :: Polinomio -> Polinomio -> Variable -> Bool
prop_deriv_prod p q x = deriv (p*q) x == (deriv p x)*q + p*(deriv q x) 

-- ---------------------------------------------------------------------
-- ** Transformación de proposiciones en polinomios
-- ---------------------------------------------------------------------

-- (tr f) es el polinomio correspondiente a la fórmula f.
tr :: FProp -> Polinomio
tr T          = uno
tr F          = cero
tr (Atom p)   = P [M [p]]
tr (Neg p)    = uno + (tr p)
tr (Conj a b) = (tr a) * (tr b)
tr (Disj a b) = (tr a) + (tr b) + ((tr a) * (tr b))
tr (Impl a b) = uno + ((tr a) + ((tr a) * (tr b)))
tr (Equi a b) = uno + ((tr a) + (tr b))

pro_tr_bien_definida :: FProp -> Bool
pro_tr_bien_definida f = esPolinomio (tr f)

-- ---------------------------------------------------------------------
-- ** Transformación de polinomios en proposiciones
-- ---------------------------------------------------------------------

-- (theta2 m) es la fórmula correspondiente al polinomio p según las
-- siguientes reglas:
--    theta 0     = F
--    theta (a+b) = no ((theta a) ↔ (theta b))
theta :: Polinomio -> FProp
theta (P ms) = thetaAux ms

thetaAux :: [Monomio] -> FProp
thetaAux []     = F
thetaAux [m]    = theta2 m
thetaAux (m:ms) = no ((theta2 m) ↔ (theta (P ms)))

-- (theta2 m) es la fórmula correspondiente al monomio m según las
-- siguientes reglas:
--    theta2 1     = T
--    theta2 (x_i) = p_i
--    theta2 (a*b) = (theta2 a) ∧ (theta2 b)
theta2 :: Monomio -> FProp
theta2 (M vs) = theta2Aux vs

theta2Aux :: [SimboloProposicional] -> FProp
theta2Aux []     = T
theta2Aux [v]    = Atom v
theta2Aux (v:vs) = Conj (Atom v) (theta2Aux vs)

prop_theta_tr :: FProp -> Bool
prop_theta_tr p = equivalentes (theta (tr p)) p

prop_tr_theta :: Polinomio -> Bool
prop_tr_theta p = tr (theta p) == p

-- ---------------------------------------------------------------------
-- ** Derivación de fórmulas proposicionales
-- ---------------------------------------------------------------------

-- (derivP f v) es la derivada de la fórmula proposicional f respecto de
-- la variable v. Por ejemplo,
--    *Polinomios> derivP (p ∧ q → r) "p"
--    no (q ↔ (q ∧ r))
--    *Polinomios> derivP (p ∧ q → r) "q"
--    no (p ↔ (p ∧ r))
--    *Polinomios> derivP (p ∧ q → r) "r"
--    (p ∧ q)
--    *Polinomios> derivP (p ∧ q → p ∨ q) "p"
--    F
derivP :: FProp -> SimboloProposicional -> FProp
derivP f v = theta (deriv (tr f) v)

-- (sustituir f v g) es la fórmula obtenida sustituyendo en la fórmula f
-- la variable v por la fórmula g.
sustituir :: FProp -> SimboloProposicional -> FProp -> FProp
sustituir T  _ _           = T
sustituir F  _ _           = F
sustituir (Atom x) v g 
    | x == v               = g
    | otherwise            = (Atom x)
sustituir (Neg f) v g      = Neg (sustituir f v g)
sustituir (Disj f1 f2) v g = Disj (sustituir f1 v g) (sustituir f2 v g)
sustituir (Conj f1 f2) v g = Conj (sustituir f1 v g) (sustituir f2 v g)
sustituir (Impl f1 f2) v g = Impl (sustituir f1 v g) (sustituir f2 v g)
sustituir (Equi f1 f2) v g = Equi (sustituir f1 v g) (sustituir f2 v g)

-- Proposición 1 (p.6) del artículo de Calculemus.
prop_derivP_sustituir :: FProp -> Bool
prop_derivP_sustituir f = 
    and [equivalentes (derivP f x) 
                      (no (sustituir f x (no (Atom x))) ↔ f) |
         x <- variablesProp f]

variablesProp f = [v | (Atom v) <- simbolosPropForm f]

-- ---------------------------------------------------------------------
-- ** La regla de independencia (regla delta)
-- ---------------------------------------------------------------------

-- (indep p x) es el polinomio formado por los monomios de que no
-- contienen la variable x. Por ejemplo,
--    *Polinomios> indep (P[M["x","y"],M["y","u"],M ["z"]]) "x"
--    y*u+z
indep :: Polinomio -> Variable -> Polinomio
indep (P ms) x = P [M m | (M m) <- ms, notElem x m]

delta :: Polinomio -> Polinomio -> Variable -> Polinomio
delta a1 a2 v = uno + ((uno+a1*a2)*(uno+a1*c2+a2*c1+c1*c2))
    where
      c1 = deriv a1 v
      c2 = deriv a2 v

delta' :: Polinomio -> Polinomio -> Variable -> Polinomio
delta' a1 a2 v = uno + (uno+b1*b2)*(uno+(b1+c1)*(b2+c2))
    where
      c1 = deriv a1 v
      c2 = deriv a2 v
      b1 = indep a1 v
      b2 = indep a2 v

prop_equiv_delta_delta' :: Polinomio -> Polinomio -> Bool
prop_equiv_delta_delta' a1 a2 =
    and [delta a1 a2 v == delta' a1 a2 v | v <- variablesPol (a1+a2)]

variablesMon :: Monomio -> [Variable]
variablesMon (M vs) = vs

variablesPol :: Polinomio -> [Variable]
variablesPol (P [])     = []
variablesPol (P (m:ms)) = (variablesMon m) `union` (variablesPol (P ms))

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

-- 1. "Zhegalkin polynomial" en Wikipedia.
-- 2. "Conservative retractions of propositional logic theories by means of
--    boolean derivatives. Theoretical foundations"
-- 3. POLYBORI-A_Grobner_basis_framework_for_Boolean_polynomials.pdf
-- 4. M. Clegg, J. Edmonds y R. Impagliazzo (1996). Using the Groebner
--    basis algorithm to find proofs of unsatisfiability. pp. 174–183.
