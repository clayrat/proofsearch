module Crit

import Data.Fuel
import Data.So
import Decidable.Decidable
import Search.HDecidable
import Search.Properties
import Diag
import CTL
import GCL

%default total

record State where
  constructor MkState
  intent1 : Bool
  intent2 : Bool
  turn    : Nat
  inCS1   : Bool
  inCS2   : Bool

CS1 : GCL State
CS1 = Update (\st => { inCS1 := True } st) `Seq` (
      Skip `Seq`
      Update (\st => { inCS1 := False } st))

CS2 : GCL State
CS2 = Update (\st => { inCS2 := True } st) `Seq` (
      Skip `Seq`
      Update (\st => { inCS2 := False } st))

petersons1 : GCL State
petersons1 = Update (\st => { intent1 := True } st) `Seq` (
             Update (\st => { turn := 0 } st) `Seq` (
             await (\st => not st.intent2 || st.turn == 1) `Seq` (
             CS1 `Seq`
             Update (\st => {intent1 := False } st))))

petersons2 : GCL State
petersons2 = Update (\st => { intent2 := True } st) `Seq` (
             Update (\st => { turn := 1 } st) `Seq` (
             await (\st => not st.intent1 || st.turn == 0) `Seq` (
             CS2 `Seq`
             Update (\st => {intent2 := False } st))))

petersons : Diagram (GCL State, GCL State) State
petersons = toDiag petersons1 `parDia` toDiag petersons2

allSkip : (GCL State, GCL State) -> Type
allSkip (a , b) = (a = Skip, b = Skip)

Termination : Formula (GCL State, GCL State) State
Termination = AF $ Guard $ const allSkip

isTermination : MC $ Termination
isTermination = AFM $ now $ \_,ld => MkHDec (isTerm ld) (sound ld)
  where
    isTerm : (GCL State, GCL State) -> Bool
    isTerm (a, b) = isYes (isSkip a) && isYes (isSkip b)

    sound : (ld : (GCL State, GCL State)) -> So (isTerm ld) -> allSkip ld
    sound (a, b) sit with (isSkip a)
      sound (a, b) sit | Yes p with (isSkip b)
        sound (a, b) sit | Yes p | Yes q = (p, q)
        sound (a, b) sit | Yes p | No q  = absurd sit
      sound (a, b) sit | No p = absurd sit

Mutex : Formula (GCL State, GCL State) State
Mutex = AG $ Guard $ \s,_ => So (not $ s.inCS1 && s.inCS2)

---

decSo : (b : Bool) -> Dec (So b)
decSo True  = Yes Oh
decSo False = No uninhabited

---

isMutex : MC Mutex
isMutex = AGM $ now $ \s,_ => decSo (not $ s.inCS1 && s.inCS2)

SF : Formula (GCL State, GCL State) State
SF = And (AF $ Guard $ \s,_ => So s.inCS1)
         (AF $ Guard $ \s,_ => So s.inCS2)

isSf : MC SF
isSf = AndM (AFM $ now $ \s,_ => decSo s.inCS1)
            (AFM $ now $ \s,_ => decSo s.inCS2)

initState : State
initState = MkState { inCS1 = False
                    , inCS2 = False
                    , intent1 = False
                    , intent2 = False
                    , turn = 0
                    }

tree : CT (GCL State, GCL State) State
tree = model petersons initState

petersonsSearch : Prop [Nat] (DPair Nat (\arg => And (And Mutex SF) Termination arg Crit.tree))
petersonsSearch = exists $ (AndM (AndM isMutex isSf) isTermination) tree

--petersonsCorrect : Sat Crit.tree (And (And Mutex SF) Termination)
--petersonsCorrect = diSat $ snd $ check (limit 10) petersonsSearch
