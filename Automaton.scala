// In the current formulation, the automaton might not be finite.

package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.math._
import stainless.proof._

import set._

object DFA {

  def apply[State, Sym](nfa: NFA[State, Sym]): DFA[Set[State], Sym] = {
    DFA({ (s: Set[State], w: Sym) => nfa.epsClosure(nfa.move(s, Some(w))) })
  }

  def dfaEquivNfa[State, Sym](nfa: NFA[State, Sym], states: Set[State],
                              word: List[Sym]): Boolean = {
    require(nfa.epsClosed(states))
    val dfa = DFA(nfa)

    nfa.run(states, word) == dfa.run(states, word)
  }.holds because {
    val dfa = DFA(nfa)

    word match {
      case Nil() => {
        nfa.run(states, word)  ==| trivial               |
        nfa.epsClosure(states) ==| nfa.epsClosed(states) |
        states                 ==| trivial               |
        dfa.run(states, word)
      }.qed

      case (w :: ws) => {
        dfa.run(states, word)                                  ==| trivial |
        dfa.run(dfa.move(states, w), ws)                       ==| trivial |
        dfa.run(dfa.trans(states, w), ws)                      ==| trivial |
        dfa.run(nfa.epsClosure(nfa.move(states, Some(w))), ws) ==| dfaEquivNfa(nfa, nfa.epsClosure(nfa.move(states, Some(w))), ws) |
        nfa.run(nfa.epsClosure(nfa.move(states, Some(w))), ws) ==| trivial |
        nfa.run(states, word)
      }.qed
    }
  }

}

case class DFA[State, Sym](trans: (State, Sym) => State) {

  def move(state: State, w: Sym): State = trans(state, w)

  def run(state: State, word: List[Sym]): State = {
    word match {
      case Nil() => state
      case (w :: ws) => run(move(state, w), ws)
    }
  }

}

// We represent ε-moves as by passing a None() to the transition function.
// The ε character/word is never representend explicitly.

case class NFA[State, Sym](trans: (State, Option[Sym]) => Set[State]) {
  def move(states: Set[State], w: Option[Sym]): Set[State] = {
    states match {
      case (ss + s) => trans(s, w) ++ move(ss, w)
      case _ => Set.empty
    }
  }

  def run(states: Set[State], word: List[Sym]): Set[State] = {
    word match {
      case Nil() => epsClosure(states)
      case (w :: ws) =>
        val newStates = move(states, Some(w))
        run(epsClosure(newStates), ws)
    }
  }

  def epsClosure(states: Set[State]): Set[State] = {
    val newStates = move(states, None())

    if (newStates == states) newStates
    else epsClosure(newStates)
  } ensuring { epsClosed _ }

  def epsClosed(states: Set[State]): Boolean = {
    states == epsClosure(states)
  }

}
