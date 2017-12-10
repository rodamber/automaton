package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.math._
import stainless.proof._

import set._


case class Automaton[State, Sym](
  validStates : Set[State],
  trans       : (State, Sym) => Set[State]
) {
  require {
    forall((s: State, w: Sym) => trans(s, w) subsetOf validStates)
  }

  def move(states: Set[State], w: Sym): Set[State]  = {
    states match {
      case (ss + s) => trans(s, w) ++ move(ss, w)
      case _ => Set.empty
    }
  }

  def run(states: Set[State], word: List[Sym]): Set[State] = {
    word match {
      case Nil() => states
      case (w :: ws) => run(move(states, w), ws)
    }
  }

  def det: Automaton[Set[State], Sym] = {
    Automaton(validStates.powerSet, { (s: Set[State], w: Sym) => move(s, w) })
  } ensuring { isDeterministic _ }

  def isDeterministic: Boolean = forall {
    (s: State, w: Sym) => trans(s, w).size == 1
  }

  def detSound(states: Set[State], word: List[Sym]): Boolean = {
    set(run(states, word)) == det.run(set(states), from)
  }.holds

}
