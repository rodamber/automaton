package props

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

object Props {

  def strictSubsetOf[T](s1: Set[T], s2: Set[T]): Boolean = {
    s1.subsetOf(s2) && s1 != s2
  }

  def a[T](s: Set[T], t: T): Boolean = {
    require(s contains t)

    val n = s - t
    strictSubsetOf(n, s)
  }.holds

  def b[T](s1: Set[T], s2: Set[T], t: T): Boolean = {
    require(s1.subsetOf(s2) && s2.contains(t))
    (s1 + t).subsetOf(s2)
  }.holds

  def c[T](f: Set[T] => Set[T], s1: Set[T], s2: Set[T]): Boolean = {
    require(forall { (s: Set[T]) => strictSubsetOf(s, f(s)) } && s1.subsetOf(s2))

    if (s1 == s2) {
      true
    } else {
      c(f, f(s1), s2)
    }
  }


}
