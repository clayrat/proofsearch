module Crit

import Diag
import GCL

%default total

record State where
  constructor MkState
  intent1 : Bool
  intent2 : Bool
  turn    : Nat
  inCS1   : Bool
  inCS2   : Bool

initialState : State
initialState = MkState { inCS1 = False
                       , inCS2 = False
                       , intent1 = False
                       , intent2 = False
                       , turn = 0
                       }

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