// In the current formulation, the automaton might not be finite.

package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.math._
import stainless.proof._

import set._
import SetSpecs._
import NFASpecs._

object DFA {

  def apply[State, Sym](nfa: NFA[State, Sym]): DFA[Set[State], Sym] = {

    val move = { (s: Set[State], w: Sym) =>
      nfa.epsClosure(nfa.move(s, Some(w)))
    }

    val initialState = nfa.epsClosure(Set(nfa.initialState))
    val isFinal = { (s: Set[State]) => s exists nfa.isFinal }

    DFA(move, initialState, isFinal )
  }

  def lemma[State, Sym](nfa: NFA[State, Sym], states: Set[State],
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
      case (w :: ws) =>
        val step = nfa.move(states, Some(w))

        { dfa.run(states, word)             ==| trivial                              |
          dfa.run(dfa.move(states, w), ws)  ==| trivial                              |
          dfa.run(dfa.move(states, w), ws)  ==| trivial                              |
          dfa.run(nfa.epsClosure(step), ws) ==| lemma(nfa, nfa.epsClosure(step), ws) |
          nfa.run(nfa.epsClosure(step), ws) ==| trivial                              |
          nfa.run(states, word)
        }.qed
    }
  }

  def dfaNfaEquiv[State, Sym](nfa: NFA[State, Sym], word: List[Sym]): Boolean = {
    val dfa = DFA(nfa)
    val init = nfa.epsClosure(Set(nfa.initialState))

    (nfa.accepts(word) == dfa.accepts(word)) because {
      nfa.accepts(word)                                   ==| trivial                |
      nfa.run(init, word).exists(nfa.isFinal)             ==| lemma(nfa, init, word) |
      dfa.run(init, word).exists(nfa.isFinal)             ==| trivial                |
      dfa.run(dfa.initialState, word).exists(nfa.isFinal) ==| trivial                |
      dfa.isFinal(dfa.run(dfa.initialState, word))        ==| trivial                |
      dfa.accepts(word)
    }.qed
  }.holds
}

case class DFA[State, Sym](
  move: (State, Sym) => State,
  initialState: State,
  isFinal: State => Boolean
) {
  def run(state: State, word: List[Sym]): State = {
    word match {
      case Nil() => state
      case (w :: ws) => run(move(state, w), ws)
    }
  }

  def accepts(word: List[Sym]): Boolean = {
    isFinal(run(initialState, word))
  }

}

// We represent ε-moves as by passing a None() to the transition function.
// The ε character/word is never representend explicitly.

case class NFA[State, Sym](
  validStates : Set[State],
  move: (State, Option[Sym]) => Set[State],
  initialState: State,
  isFinal: State => Boolean
) {
  require {
    forall { (s: State, w: Option[Sym]) => move(s, w) subsetOf validStates } &&
    validStates.contains(initialState)
  }

  def move(states: Set[State], w: Option[Sym]): Set[State] = {
    states match {
      case (x + xs) => move(x, w) ++ move(xs, w)
      case _  => Set()
    }
  } // ensuring { res => res subsetOf validStates }

  def run(states: Set[State], word: List[Sym]): Set[State] = {
    require(states.subsetOf(validStates))
    word match {
      case Nil() => epsClosure(states)
      case (w :: ws) =>
        val newStates = move(states, Some(w))
        assert(moveValid(this, states, Some(w)))
        run(epsClosure(newStates), ws)
    }
  } ensuring { res => res subsetOf validStates }

  def epsClosure(states: Set[State]): Set[State] = {
    require(states.subsetOf(validStates))

    assert((states.size <= validStates.size) because sizeSubsetOf(states, validStates))
    decreases(validStates.size - states.size + 1)

    val newStates: Set[State] = states ++ move(states, None[Sym]())

    assert(moveValid(this, states, None[Sym]()))
    assert(unionSubset(states, move(states, None[Sym]()), validStates))

    assert(states subsetOf newStates)

    if (newStates.neq(states)) {
      newStates
    } else {
      assert(sizeStrictSubsetOf(states, newStates))
      assert(newStates.size > states.size)
      epsClosure(newStates)
    }
  } ensuring { res =>
    epsClosed(res) && (res subsetOf validStates)
  }

  def epsClosed(states: Set[State]): Boolean = {
    require(states.subsetOf(validStates) && sizeSubsetOf(states, validStates))
    states == epsClosure(states)
  }

  def accepts(word: List[Sym]): Boolean = {
    val start = epsClosure(Set(initialState))
    run(start, word) exists isFinal
  }

}

object NFASpecs {

  def moveValid[S,W](nfa: NFA[S,W], states: Set[S], w: Option[W]): Boolean = {
    nfa.move(states, w) subsetOf nfa.validStates
  }.holds because {
    states match {
      case (x + xs) => moveValid(nfa, xs, w) &&
          unionSubset(nfa.move(x, w), nfa.move(xs, w), nfa.validStates)
      case _ => trivial
    }
  }

}
