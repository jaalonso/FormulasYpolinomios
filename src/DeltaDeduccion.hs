-- Module      : DeltaDeduccion
-- Description : Deducción con la regla delta (o de la independencia)
-- Copyright   : José A. Alonso
-- License     : GPL-3
-- Maintainer  : JoseA.Alonso@gmail.com
-- Stability   : Provisional

module DeltaDeduccion where

-- ---------------------------------------------------------------------
-- Librerías auxiliares                                               --
-- ---------------------------------------------------------------------

import Logica           ( FProp ( T
                                , F
                                , Atom
                                , Neg
                                , Conj
                                , Disj
                                , Impl
                                , Equi
                                )
                        , SimboloProposicional
                        , equivalentes
                        , esConsecuencia
                        , esInconsistente
                        , esValida
                        , no
                        , p
                        , q
                        , r
                        , simbolosPropForm
                        , (∧)
                        , (∨)
                        , (→)
                        , (↔)
                        )
import PolinomiosF2     ( Monomio (M)
                        , Polinomio (P)
                        , Variable
                        , cero
                        , deriv
                        , mUno
                        , uno
                        )
import Transformaciones ( theta
                        , tr
                        )

import Data.List ( delete
                 , union
                 , nub
                 )
import Test.QuickCheck

-- ---------------------------------------------------------------------
-- * Derivación de fórmulas proposicionales
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
-- * La regla de independencia (regla delta)
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
-- * Adecuación y completitud de la regla de independencia
-- ---------------------------------------------------------------------

-- | Comprueba que la regla delta es adecuada: es decir que, para toda
-- fórmulas f1 y f2 y toda variable x de ellas, la fórmula (deltaP f1 f2 x) 
-- es consecuencia de f1 y f2.
--
-- >>> quickCheck prop_adecuacion_deltaP
-- +++ OK, passed 100 tests.
prop_adecuacion_deltaP :: FProp -> FProp -> Bool
prop_adecuacion_deltaP f1 f2 = 
    and [esConsecuencia [f1, f2] (deltaP f1 f2 x) |
         x <- variablesProp (f1 ∧ f2)]

-- | (pares xs) es la lista de los pares de elementos xs con el primero
-- menor o igual que el segundo. Por ejemplo,
--
-- >>> pares [1..4]
-- [(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]
pares :: [a] -> [(a,a)]
pares []     = []
pares [x]    = [(x,x)]
pares (x:xs) = [(x,y) | y <- (x:xs)] ++ pares xs

-- | (derivadas ps x) es la lista de los polinomios obtenidos aplicando
-- la regla delta a dos polinomios de ps respecto de la variable x. Por
-- ejemplo,
--
-- >>> derivadas [P[M["x","y"],M["y","z"]],P[M["a","y"],M["y"]]] "y"
-- [x+z,a*x+a*z+x+z,1+a]
derivadas :: [Polinomio] -> Variable -> [Polinomio]
derivadas ps x =
  delete uno (nub [delta p1 p2 x | (p1,p2) <- pares ps])

-- | (derivadasP fs x) es la lista de las proposiciones obtenidas aplicando
-- la regla deltaP a dos fórmulas de fs respecto de la variable x. Por
-- ejemplo,
--
-- >>> derivadasP [p → q ∨ r, r → p] "q"
-- [¬(⊤ ↔ ¬((p ∧ r) ↔ r))]
-- >>> derivadasP [p → q ∨ r, r → q] "q"
-- []
derivadasP :: [FProp] -> SimboloProposicional -> [FProp]
derivadasP fs x =
  delete T (nub [deltaP f1 f2 x | (f1,f2) <- pares fs])

-- | (deltaRefutable ps) se verifica si ps es refutable mediante la regla
-- delta. Por ejemplo,
--
-- >>> deltaRefutable [P[mUno,M["p"],M["p","q"]],P[M["p"]],P[mUno,M["q"]]]
-- True
-- >>> deltaRefutable [P[mUno,M["p"],M["p","q"]],P[M["p"]],P[mUno,M["r"]]]
-- False
deltaRefutable :: [Polinomio] -> Bool
deltaRefutable [] = False
deltaRefutable ps =
  cero `elem` ps || deltaRefutable (derivadas ps (eligeVariable ps))
  where eligeVariable ps = head (concat [variablesPol p | p <- ps])

-- | (deltaRefutableP fs) se verifica si fs es refutable mediante la regla
-- delta. Por ejemplo,
--
-- >>> deltaRefutableP [p → q, p, no q]
-- True
-- >>> deltaRefutableP [p → q, p, no r]
-- False
deltaRefutableP :: [FProp] -> Bool
deltaRefutableP fs = deltaRefutable [tr f | f <- fs]

-- | (deltaRefutableP' fs) se verifica si fs es refutable mediante la regla
-- delta. Por ejemplo,
-- 
-- >>> deltaRefutableP' [p → q, p, no q]
-- True
-- >>> deltaRefutableP' [p → q, p, no r]
-- False
deltaRefutableP' :: [FProp] -> Bool
deltaRefutableP' [] = False
deltaRefutableP' fs =
  F `elem` fs || deltaRefutableP' (derivadasP fs (eligeVariable fs))
  where eligeVariable gs = head (concat [variablesProp g | g <- gs])

-- | Comprueba que las funciones deltaRefubleP y deltaRefutableP' son
-- equivalentes.
--
-- >>> quickCheck prop_def_alt_deltaRefutableP
-- +++ OK, passed 100 tests.
prop_def_alt_deltaRefutableP :: [FProp] -> Bool
prop_def_alt_deltaRefutableP fs =
  deltaRefutableP fs == deltaRefutableP' fs

-- | Comprueba que la regla delta es adecuada y completa; es decir, para
-- todo conjunto de fórmulas fs, fs es inconsistente si y sólo si es
-- delta refutable.
--
-- >>> quickCheck prop_adecuacion_completitud_deltaP
-- +++ OK, passed 100 tests.
prop_adecuacion_completitud_deltaP :: [FProp] -> Bool
prop_adecuacion_completitud_deltaP fs = 
  esInconsistente fs == deltaRefutableP fs

-- | (deltaDemostrable fs g) se verifica si g es demostrable a partir de
-- fs usando la regla delta. Por ejemplo,
--
-- >>> deltaDemostrable [p → q, q → r] (p → r)
-- True
-- >>> deltaDemostrable [p → q, q → r] (r → p)
-- False
deltaDemostrable :: [FProp] -> FProp -> Bool
deltaDemostrable fs g =
  deltaRefutableP ((no g):fs)

-- | Comprueba que la regla delta es adecuada y completa; es decir, para
-- todo conjunto de fórmulas fs y toda fórmula g, g es consecuencia de
-- fs si y sólo si es g es delta demostrable a partir de fs.
--
-- >>> quickCheck prop_adecuacion_completitud_delta_2
-- +++ OK, passed 100 tests.
prop_adecuacion_completitud_delta_2 :: [FProp] -> FProp -> Bool
prop_adecuacion_completitud_delta_2 fs g =
  esConsecuencia fs g == deltaDemostrable fs g

-- | (deltaTeorema f) se verifica si f es un teorema mediante la regla
-- delta; es decir, si la negación de f es delta refutable. Por ejemplo,
--
-- >>> deltaTeorema ((p → q) ∨ (q → p))
-- True
-- >>> deltaTeorema ((p → q) ∨ (q → r))
-- True
-- >>> deltaTeorema ((p → q) ∨ (r → q))
-- False
deltaTeorema :: FProp -> Bool
deltaTeorema f = deltaRefutableP [no f]

-- | Comprueba que la regla delta es adecuada y completa; es decir, que
-- para toda fórmula f, f es válida si y sólo si es un delta teorema.
--
-- >>> quickCheck prop_adecuacion_completitud_delta_3
-- +++ OK, passed 100 tests.
prop_adecuacion_completitud_delta_3 :: FProp -> Bool
prop_adecuacion_completitud_delta_3 f =
  esValida f == deltaTeorema f

-- ---------------------------------------------------------------------
-- * Bibliografía
-- ---------------------------------------------------------------------

-- $doc
-- 
-- * Wikipedia: [Zhegalkin polynomial](http://bit.ly/2tYsY9A).
-- * G.A. Aranda, J. Borrego y  M.M. Fernández (2009)
--   [Conservative retractions of propositional logic theories by means
--    of boolean derivatives. Theoretical foundations](http://bit.ly/2tYdN0d).
-- * M. Brickenstein y A. Dreyer:
--   [PolyBoRi: A Gröbner basis framework for Boolean
--    polynomials](http://bit.ly/2tuf4sA). 
-- * M. Clegg, J. Edmonds y R. Impagliazzo (1996):
--   [Using the Groebner basis algorithm to find proofs of
--    unsatisfiability](http://bit.ly/2tY7wl5). 
