module CTL

import Data.Nat
import Data.List.Quantifiers
import Decidable.Equality
import Search.HDecidable
import Diag

%default total

public export
data CT : Type -> Type -> Type where
  At : (l, s) -> Inf (List (CT l s)) -> CT l s

public export
model : Diagram l s -> s -> CT l s
model (TD tr i) st = follow (i, st)
  where
  follow : (l, s) -> CT l s
  followAll : List (l,s) -> List (CT l s)
  follow ls = At ls (followAll (tr ls))
  followAll [] = []
  followAll (ls :: lss) = follow ls :: followAll lss

public export
Formula : Type -> Type -> Type
Formula l s = (depth : Nat) -> (tree : CT l s) -> Type

---

public export
data LTE'  : (n, m : Nat) -> Type where
  LTERefl : LTE' n n
  LTEStep : LTE' n m -> LTE' n (S m)

---

public export
data Sat : (m : CT l s) -> (f : Formula l s) -> Type where
  Satisfies : (0 d0 : Nat) -> ({0 d : Nat} -> LTE' d0 d -> f d m) -> Sat m f

interface DepthInv (0 f : Formula l s) where
  prf : {0 n : Nat} -> {0 m : CT l s} -> f n m -> f (S n) m

public export
diSat : {f : Formula l s} -> DepthInv f => f n m -> Sat m f
diSat fnm = Satisfies n (diLte fnm)
  where
  diLte : f n' m -> LTE' n' n'' -> f n'' m
  diLte fn  LTERefl      = fn
  diLte fn (LTEStep lte) = prf {f} $ diLte fn lte

data TrueF : Formula l s where
  TT : TrueF n m

DepthInv TrueF where
  prf TT = TT

public export
data Guard : (0 g : s -> l -> Type) -> Formula l s where
  HereG : {0 st : s} -> {0 ld : l} -> {0 ms : Inf (List (CT l s))} ->
          g st ld -> Guard g d (At (ld, st) ms)

DepthInv (Guard p) where
  prf (HereG x) = HereG x

public export
data And : (f, g : Formula l s) -> Formula l s where
  MkAnd : f n m -> g n m -> And f g n m

(DepthInv f, DepthInv g) => DepthInv (And f g) where
  prf (MkAnd fnm gnm) = MkAnd (prf {f} fnm) (prf {f=g} gnm)

data AU : (f, g : Formula l s) -> Formula l s where
  HereA  : g n t -> AU f g (S n) t
  ThereA : f n (At st ms) -> All (AU f g n) ms -> AU f g (S n) (At st ms)

(DepthInv f, DepthInv g) => DepthInv (AU f g) where
  prf (HereA x)     = HereA $ prf {f=g} x
  prf (ThereA x xs) = ThereA (prf {f} x) (mapProperty (prf {f=AU f g}) xs)

data EU : (f, g : Formula l s) -> Formula l s where
  HereE  : g n t -> EU f g (S n) t
  ThereE : f n (At st ms) -> Any (EU f g n) ms -> EU f g (S n) (At st ms)

(DepthInv f, DepthInv g) => DepthInv (EU f g) where
  prf (HereE x)     = HereE $ prf {f=g} x
  prf (ThereE x xs) = ThereE (prf {f} x) (mapProperty (prf {f=EU f g}) xs)

public export
AF : Formula l s -> Formula l s
AF = AU TrueF

EF : Formula l s -> Formula l s
EF = EU TrueF

data Completed : Formula l s where
  Cmpl : Force ms = [] -> Completed n (At st ms)

DepthInv Completed where
  prf (Cmpl p) = Cmpl p

public export
AG : Formula l s -> Formula l s
AG f = AU f (And f Completed)

EG : Formula l s -> Formula l s
EG f = EU f (And f Completed)

-- TODO looks suspicious
public export
MC : {l, s : Type} -> Formula l s -> Type
MC f = (t : CT l s) -> (d : Nat) -> HDec (f d t)

public export
now : AnHDec hdec => {g : s -> l -> Type} ->
     ((st : s) -> (ld : l) -> hdec (g st ld)) ->
     MC (Guard g)
now p (At (ld', st') ms) _ = [| HereG (toHDec (p st' ld')) |]

isCompleted : MC Completed
isCompleted (At st ms) _ = Cmpl <$> isEmpty ms
  where
  isEmpty : (n : List t) -> HDec (n = [])
  isEmpty []       = yes Refl
  isEmpty (_ :: _) = no

public export
AndM : MC f -> MC g -> MC (And f g)
AndM a b m n = [| MkAnd (a m n) (b m n) |]

AUM : MC f -> MC g -> MC (AU f g)
AUM _  _  _             Z    = no
AUM mf mg t@(At st ms) (S d) = [| HereA (mg t d) |]
                           <|> [| ThereA (mf t d) (all ms (\x => AUM mf mg x d)) |]

EUM : MC f -> MC g -> MC (EU f g)
EUM _  _  _             Z    = no
EUM mf mg t@(At st ms) (S d) = [| HereE (mg t d) |]
                           <|> [| ThereE (mf t d) (any ms (\x => EUM mf mg x d)) |]

EFM : MC f -> MC (EF f)
EFM = EUM (\_, _ => pure TT)

public export
AFM : MC f -> MC (AF f)
AFM = AUM (\_, _ => pure TT)

EGM : MC f -> MC (EG f)
EGM p = EUM p (AndM p isCompleted)

public export
AGM : MC f -> MC (AG f)
AGM p = AUM p (AndM p isCompleted)

tree : CT ((), ()) Nat
tree = model (parDia hiHorse loRoad) 0

reaches10 : HDec (EF (Guard (\st, _ => st = 10)) 20 CTL.tree)
reaches10 = EFM (now $ \st, _ => decEq st 10) tree 20

--proof10 : Sat CTL.tree (EF (Guard (\st, _ => st = 10)))
--proof10 = diSat $ reaches10.evidence ?wat
