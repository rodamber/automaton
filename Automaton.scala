package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.math._
import stainless.proof._


object Utils {

  def isSubsequenceOf[T](L: List[T], S: List[T]): Boolean = {
    (L, S) match {
      case (Nil(), _) => true
      case (_, Nil()) => false
      case (Cons(l, ls), Cons(s, ss)) => {
        if (l == s) isSubsequenceOf(ls, ss)
        else isSubsequenceOf(L, ss)
      }
    }
  } ensuring { _ ==> (L.content subsetOf S.content) }

}

import Utils._

case class Automaton[State](
  S: List[State],                  // internal states
  M: (State, Char) => List[State], // transition function
  S0: State,                       // initial states
  F: List[State]                   // final states
) {
  require(S.nonEmpty)

  require(forall((s: State, w: Char) => isSubsequenceOf(M(s, w), S)))

  require(S contains S0)
  require(isSubsequenceOf(F, S))


  def validSet(s: List[State]): Boolean = {
    isSubsequenceOf(s, S)
  }


  def lessThan(s: State, t: State): Boolean = {
    require(S contains s)
    require(S contains t)

    lessThanAux(s, t, S)
  }


  def lessThanAux(s: State, t: State, l: List[State]): Boolean = {
    require(l contains s)
    require(l contains t)

    l match {
      case Cons(x, xs) => 
        if      (s == x) true
        else if (t == x) false
        else             lessThanAux(s, t, xs)
    }
  }


  // === Verified ==============================================================


  // flatMap
  // Removes repeated elements. Strictly ordered.
  def unionMap(set: List[State], f: State => List[State]): List[State] = {
    require(validSet(set))
    require(forall((s: State) => validSet(f(s))))

    set match {
      case Nil()      => Nil()
      case Cons(h, t) => merge(f(h), unionMap(t, f))
    }
  }


  // Removes repeated elements. Strictly ordered.
  def merge(a: List[State], b: List[State]): List[State] = {
    require(validSet(a))
    require(validSet(b))

    assert(a.content subsetOf S.content)
    assert(b.content subsetOf S.content)

    (a, b) match {
      case (_, Nil()) => a
      case (Nil(), _) => b
      case (Cons(x, xs), Cons(y, ys)) =>
        assert(S contains x)
        assert(S contains y)

        if (x == y)              x :: merge(xs, ys) // FIXME
        else if (lessThan(x, y)) x :: merge(xs, b)  // FIXME
        else                     y :: merge(a, ys)
    }
  }


  def validSubsets[A](l: List[A]): List[List[A]] = {
    l match {
      case Nil()      => List(Nil())
      case Cons(h, t) =>
        val ps = validSubsets(t)

        // FIXME: Uses map...
        ps ++ ps.map { h :: _ }
    }

    // FIXME: Not obvious at all.
  } // ensuring { res => res.forall(validSet(_)) }


  def isDeterministic: Boolean =
    forall { (s: State, c: Char) =>
      (S contains s) ==> (M(s, c).size <= 1)
    }


  def isAcceptingPath(states: List[State], word: List[Char]): Boolean = {
    require(states.content subsetOf S.content)

    states match {
      case Nil() => false
      case Cons(s, _) => F.contains(s) && isPath(states, word, S0)
    }
  }


  def isPath(states: List[State], word: List[Char], from: State): Boolean = {
    require(states.content subsetOf S.content)
    require(S contains from)

    (states, word) match {
      case (Cons(s, Nil()), Nil()) =>
        from == s
      case (Cons(t, ss @ Cons(s, _)), Cons(w, ws)) =>
        M(s, w).contains(t) && isPath(ss, ws, from)
      case _ =>
        false
    }
  }


  def mkPath(word: List[Char], from: State): Option[List[State]] = {
    require(S contains from)

    word match {
      case Nil()       => Some(List(from))
      case Cons(w, ws) => mkPath(ws, from) match {
        case Some(path) => path match {
          case Cons(s, _) => M(s, w) match {
            case Cons(t, _) => Some(t :: path)
            case Nil()      => None()
          }
        }
        case None() => None()
      }
    }
  }


  // Returns the set of possible states the NFA might be in after processing the
  // word.
  def runFrom(word: List[Char], from: List[State]): List[State] = {
    require(validSet(from))

    word match {
      case Nil()       => from
      case Cons(w, ws) => runFrom(ws, unionMap(from, { M(_, w) }))
    }
  }


  // Run starting from the initial state.
  def run(word: List[Char]): List[State] = runFrom(word, List(S0))


  def accepts(word: List[Char]): Boolean = (run(word) & F).nonEmpty


  def det(): Automaton[List[State]] = {
    val valid   = validSubsets(S)
    val trans   = { (s: List[State], w: Char) => List(unionMap(s, { M(_, w) })) }
    val initial = List(S0)
    val final_  = for (s <- valid if (s & F).nonEmpty) yield s

    Automaton(valid, trans, initial, final_)
  } ensuring { res =>
    res.isDeterministic
  }


  def detSound(word: List[Char]): Boolean = {
    run(word) == det().run(word).head
  }.holds


  def detSound2(word: List[Char]): Boolean = {
    accepts(word) == det().accepts(word)
  }.holds


}
