-- Module      : Transformaciones
-- Description : Transformaciones entre fórmulas y polinomios
-- Copyright   : José A. Alonso
-- License     : GPL-3
-- Maintainer  : JoseA.Alonso@gmail.com
-- Stability   : Provisional

module Transformaciones where

-- ---------------------------------------------------------------------
-- Librerías auxiliares                                               --
-- ---------------------------------------------------------------------

import Logica
import PolinomiosF2

import Test.QuickCheck

-- ---------------------------------------------------------------------
-- * Transformación de proposiciones en polinomios
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
-- * Transformación de polinomios en proposiciones
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
