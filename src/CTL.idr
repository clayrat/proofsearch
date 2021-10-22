module CTL

import Data.Nat
import Diag

%default total

data CT : Type -> Type -> Type where
  At : (l, s) -> Inf (List (CT l s)) -> CT l s

model : Diagram l s -> s -> CT l s
model (TD tr i) st = follow (i, st)
  where
  follow : (l, s) -> CT l s
  followAll : List (l,s) -> List (CT l s)
  follow ls = At ls (followAll (tr ls))
  followAll [] = []
  followAll (ls :: lss) = follow ls :: followAll lss

Formula : Type -> Type -> Type
Formula l s = (depth : Nat) -> (tree : CT l s) -> Type

---

public export
data LTE'  : (n, m : Nat) -> Type where
  LTERefl : LTE' n n
  LTEStep : LTE' n m -> LTE' n (S m)

---

data Sat : (m : CT l s) -> (f : Formula l s) -> Type where
  Satisfies : (0 d0 : Nat) -> ({0 d : Nat} -> LTE' d0 d -> f d m) -> Sat m f

interface DepthInv (0 f : Formula l s) where
  prf : {0 n : Nat} -> {0 m : CT l s} -> f n m -> f (S n) m

diSat : {f : Formula l s} -> DepthInv f => f n m -> Sat m f
diSat @{di} fnm = Satisfies n (diLte fnm)
  where
  diLte : f n' m -> LTE' n' n'' -> f n'' m
  diLte fn  LTERefl      = fn
  diLte fn (LTEStep lte) = prf @{di} $ diLte fn lte

data TrueF : Formula l s where
  TT : TrueF n m

DepthInv TrueF where
  prf TT = TT

data Guard : (0 g : s -> l -> Type) -> Formula l s where
  Here : {0 st : s} -> {0 ld : l} -> g st ld -> Guard g d (At (ld, st) ms)

DepthInv (Guard p) where
  prf (Here x) = Here x

data And : (0 f, g : Formula l s) -> Formula l s where
  MkAnd : f n m -> g n m -> And f g n m

(DepthInv f, DepthInv g) => DepthInv (And f g) where
  prf @{(df, dg)} (MkAnd fnm gnm) = MkAnd (prf @{df} fnm) (prf @{dg} gnm)
