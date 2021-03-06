package elevate.rise

import elevate.core.strategies.predicate.rewriteResultToBoolean
import elevate.core.strategies.traversal._
import elevate.rise.rules.movement._
import elevate.rise.rules.traversal._
import elevate.rise.strategies.normalForm._
import elevate.util._
import rise.core._
import rise.core.TypedDSL._
import rise.core.TypeLevelDSL._
import rise.core.types.f32

class movement extends elevate.test_util.Tests {

  // transpose

  def betaEtaEquals(a: Rise, b: Rise): Boolean = {
    val na = BENF(a).get
    val nb = BENF(b).get
    val uab: Rise = toTDSL(na) :: nb.t
    makeClosed(uab) == makeClosed(nb)
  }

  test("**f >> T -> T >> **f") {
    val gold = λ(f => T >> **(f))

    testMultiple(
      List(
        DFNF(λ(f => *(λ(x => *(f)(x))) >> T)).get,
        toExpr(λ(f => **(f) >> T))
      ).map((topDown(`**f >> T -> T >> **f`)).apply(_).get), gold
    )
  }

  // FIXME: Not work because mapMapFBeforeTranspose is not general enough
  ignore("**f >> T - zip constraint") {
    // val test = λ(i => λ(f => (T o ***(f)) $ zip(i,i)))

    val backward: Expr =
      nFun((m, n, k) =>
        fun((m`.`k`.`f32) ->: (k`.`n`.`f32) ->: (m`.`n`.`f32) ->: f32 ->: f32 ->: (n`.`m`.`f32))
        ((a, b, c, alpha, beta) =>
          (transpose o map(fun(ac =>
            map(fun(bc =>
              (fun(x => (x * alpha) + beta * bc._2) o
                reduceSeq(fun((acc, y) => acc + (y._1 * y._2)), l(0.0f))) $
                zip(ac._1, bc._1))) $
              zip(transpose(b),ac._2)))) $
            zip(a, c)
        )
      )

    assert(topDown(mapMapFBeforeTranspose).apply(backward))
  }

  test("T >> **f -> **f >> T") {
    assert(betaEtaEquals(
      topDown(`T >> **f -> **f >> T`).apply(λ(f => T >> **(f))),
      λ(f => **(f) >> T))
    )
  }

  test("T >> ****f -> ****f >> T") {
    assert(betaEtaEquals(
      topDown(`T >> **f -> **f >> T`).apply(λ(f => T >> ****(f))),
      λ(f => ****(f) >> T))
    )
  }

  test("****f >> T -> T >> ****f") {
    assert(betaEtaEquals(
      topDown(`**f >> T -> T >> **f`).apply(λ(f => ****(f) >> T)),
      λ(f => T >> ****(f)))
    )
  }

  // split/slide

  test("S >> **f -> *f >> S") {
    assert(betaEtaEquals(
      topDown(`S >> **f -> *f >> S`).apply(λ(f => S >> **(f))),
      λ(f => *(f) >> S))
    )
  }

  test("*f >> S -> S >> **f") {
    assert(betaEtaEquals(
      topDown(splitBeforeMap).apply(λ(f => *(f) >> S)),
      λ(f => S >> **(f)))
    )
  }

  // join

  test("J >> *f -> **f >> J") {
    assert(betaEtaEquals(
      topDown(`J >> *f -> **f >> J`).apply(λ(f => J >> *(f))),
      λ(f => **(f) >> J)
    ))
  }

  test("**f >> J -> *f >> J") {
    assert(betaEtaEquals(
      topDown(`**f >> J -> J >> *f`).apply(λ(f => **(f) >> J)),
      λ(f => J >> *(f))
    ))
  }

  // special-cases

  test("T >> S -> *S >> T >> *T") {
    assert(betaEtaEquals(
      topDown(`T >> S -> *S >> T >> *T`).apply(T >> S),
      *(S) >> T >> *(T)
    ))
  }

  test("T >> *S -> S >> *T >> T") {
    assert(betaEtaEquals(
      topDown(`T >> *S -> S >> *T >> T`).apply(T >> *(S)),
      S >> *(T) >> T
    ))
  }

  test("*S >> T -> T >> S >> *T") {
    assert(betaEtaEquals(
      topDown(`*S >> T -> T >> S >> *T`).apply(*(S) >> T),
      T >> S >> *(T)
    ))
  }

  test("J >> T -> *T >> T >> *J") {
    assert(betaEtaEquals(
      topDown(`J >> T -> *T >> T >> *J`).apply(J >> T),
      *(T) >> T >> *(J)
    ))
  }

  test("T >> *J -> *T >> J >> T") {
    assert(betaEtaEquals(
      topDown(`T >> *J -> *T >> J >> T`).apply(T >> *(J)),
      *(T) >> J >> T
    ))
  }

  test("*T >> J -> T >> *J >> T") {
    assert(betaEtaEquals(
      topDown(`*T >> J -> T >> *J >> T`).apply(*(T) >> J),
      T >> *(J) >> T
    ))
  }

  test("*J >> T -> T >> *T >> J") {
    assert(betaEtaEquals(
      topDown(`*J >> T -> T >> *T >> J`).apply(*(J) >> T),
      T >> *(T) >> J
    ))
  }

  test("J >> J -> *J >> J") {
    assert(betaEtaEquals(
      topDown(`J >> J -> *J >> J`).apply(J >> J),
      *(J) >> J
    ))
  }

  test("*J >> J -> J >> J") {
    assert(betaEtaEquals(
      topDown(`*J >> J -> J >> J`).apply(*(J) >> J),
      J >> J
    ))
  }

  test("slideOverSplit") {
    assert(betaEtaEquals(
      topDown(slideBeforeSplit).apply(slide(3)(1) >> split(16)),
      slide(16+3-1)(16) >> map(slide(3)(1))
    ))
  }
}
