-- Module      : PolinomiosF2
-- Description : Polinomios en Z2/(x1^1-x1,...,xn^2-xn)
-- Copyright   : José A. Alonso
-- License     : GPL-3
-- Maintainer  : JoseA.Alonso@gmail.com
-- Stability   : Provisional

module PolinomiosF2 where

-- ---------------------------------------------------------------------
-- Librerías auxiliares                                               --
-- ---------------------------------------------------------------------

import Control.Monad ( liftM
                     , liftM2)
import Data.Char     ( chr
                     )
import Data.List     ( delete
                     , insert
                     , nub
                     , sort
                     , union
                     )
import Test.QuickCheck

-- ---------------------------------------------------------------------
-- * Variables
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
-- * Monomios
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

-- | Los monomios son arbitrarios.
instance Arbitrary Monomio where
  arbitrary = monomios

-- ---------------------------------------------------------------------
-- * Polinomios
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

-- | Los polinomios son arbitrarios.
instance Arbitrary Polinomio where
  arbitrary = polinomios

-- | Para facilitar la escritura, se hace Polinomio una instancia de
-- la clase Num. Las funciones suma y producto se definen a continuación.
instance Num Polinomio where
  (+) = suma 
  (*) = producto
  (-) = suma
  abs = undefined
  signum = undefined
  fromInteger = undefined

-- ---------------------------------------------------------------------
-- * Suma de polinomios 
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
-- * Productos de polinomios
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
-- * Derivada de polinomios
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

