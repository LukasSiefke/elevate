package elevate.rise

import elevate.core.strategies.predicate._
import elevate.rise.rules.traversal._
import elevate.core.{Failure, RewriteResult, Strategy, Success}
import rise.core._
import rise.core.types._
import rise.core.TypedDSL._

package object rules {

  case object betaReduction extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(Lambda(x, b), v) =>
        Success(substitute.exprInExpr(v, `for` = x, in = b))
      case DepApp(DepLambda(x, b), v) =>
        Success(substitute.kindInExpr(v, `for` = x, in = b))
      case _ => Failure(betaReduction)
    }
    override def toString = "betaReduction"
  }

  case object etaReduction extends Strategy[Rise]  {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case Lambda(x1, App(f, x2)) if x1 == x2 && !contains[Rise](x1).apply(f) => Success(f :: e.t)
      case _                                                                  => Failure(etaReduction)
    }
    override def toString = "etaReduction"
  }

  case object etaAbstraction extends Strategy[Rise] {
    def apply(f: Rise): RewriteResult[Rise] = f.t match {
      case FunType(_, _) =>
        val x = identifier(freshName("η"))
        Success(lambda(x, app(f, x)) :: f.t)
      case _ => Failure(etaAbstraction)
    }
    override def toString = "etaAbstraction"
  }

  // todo: remove once all rules are type-preserving
  case object inferRise extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = Success(infer(e))
  }

}
