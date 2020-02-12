package elevate.rise.rules

import elevate.core.strategies.predicate._
import elevate.core.{Failure, RewriteResult, Strategy, Success}
import elevate.rise._
import rise.core._
import rise.core.primitives._
import rise.core.TypedDSL._
import rise.core.TypeLevelDSL._
import rise.core.types.{ArrayType, DataType, FunType, IndexType}

// Describing possible movements between pairs of rise primitives
// (potentially nested in maps)

// todo: remove inspection prevention

//noinspection ScalaStyle
// todo: should all rules expect LCNF-normalized expressions as input?
object movement {

  // - Notation -
  // x >> y: piping operator, x then y
  // *f: map(f)
  // T: transpose
  // S: slide/split
  // J: join

  // transpose

  def mapMapFBeforeTranspose: Strategy[Rise] = `**f >> T -> T >> **f`
  case object `**f >> T -> T >> **f` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
        Transpose(),
        App(App(Map(), App(Map(), f)), y)) =>
          Success((typed(y) |> transpose |> map(map(f))) :: e.t)
      // LCNF
      case App(Transpose(),
      App(
      App(Map(), lamA @ Lambda(_, App(
                App(Map(), lamB @ Lambda(_, App(
      f, _))), _))),
      arg
      )
      ) if etaReduction(lamA) && etaReduction(lamB) =>
        // Success((typed(arg) |> transpose |> map(map(f))) :: e.t)
        Success((typed(arg) |> transpose |> map(fun(a => map(fun(b => typed(f)(b)))(a)))) :: e.t)
      case _ => Failure(mapMapFBeforeTranspose)
    }
    override def toString = "mapMapFBeforeTranspose"
  }

  def transposeBeforeMapMapF: Strategy[Rise] = `T >> **f -> **f >> T`
  case object `T >> **f -> **f >> T` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      App(Map() , App(Map(), f)),
      App(Transpose() , y)) =>
        Success((typed(y) |> map(map(f)) |> transpose) :: e.t)
      case _ => Failure(transposeBeforeMapMapF)
    }
    override def toString = "transposeBeforeMapMapF"
  }

  // split/slide

  private def isSplitOrSlide(s: Expr): Boolean = s match {
    case DepApp(DepApp(Slide(), _: Nat), _: Nat) => true
    case DepApp(Split(), _: Nat)                 => true
    case _                                       => false
  }

  def slideBeforeMapMapF: Strategy[Rise] = `S >> **f -> *f >> S`
  case object `S >> **f -> *f >> S` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      App(Map(), App(Map(), f)),
      App(s, y)) if isSplitOrSlide(s) =>
        Success((typed(y) |> map(f) |> untyped(s)) :: e.t)
      case _ => Failure(slideBeforeMapMapF)
    }
    override def toString = "slideBeforeMapMapF"
  }

  def mapFBeforeSlide: Strategy[Rise] = `*f >> S -> S >> **f`
  case object `*f >> S -> S >> **f` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      s,
      App(App(Map(), f), y)) if isSplitOrSlide(s) =>
        Success((typed(y) |> untyped(s) |> map(map(f))) :: e.t)
      case _ => Failure(mapFBeforeSlide)
    }
    override def toString = "mapFBeforeSlide"
  }

  // join

  def joinBeforeMapF: Strategy[Rise] = `J >> *f -> **f >> J`
  case object `J >> *f -> **f >> J` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      App(Map(), f),
      App(Join(), y)
      ) =>
        Success((typed(y) |> map(map(f)) >> join) :: e.t)
      case _ => Failure(joinBeforeMapF)
    }
    override def toString = "joinBeforeMapF"
  }

  def mapMapFBeforeJoin: Strategy[Rise] = `**f >> J -> J >> *f`
  case object `**f >> J -> J >> *f` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      Join(),
      App(App(Map(), App(Map(), f)), y)
      ) =>
        Success((typed(y) |> join |> map(f)) :: e.t)
      case _ => Failure(mapMapFBeforeJoin)
    }
    override def toString = "mapMapFBeforeJoin"
  }

  // special-cases
  // slide + transpose

  def transposeBeforeSlide: Strategy[Rise] = `T >> S -> *S >> T >> *T`
  case object `T >> S -> *S >> T >> *T` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      s,
      App(Transpose(), y)
      ) if isSplitOrSlide(s) =>
        Success((typed(y) |> map(untyped(s)) |> transpose >> map(transpose)) :: e.t)
      case _ => Failure(transposeBeforeSlide)
    }
    override def toString = "transposeBeforeSlide"
  }

  def transposeBeforeMapSlide: Strategy[Rise] = `T >> *S -> S >> *T >> T`
  case object `T >> *S -> S >> *T >> T` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      App(Map(), s),
      App(Transpose(), y)
      ) if isSplitOrSlide(s) =>
        Success((typed(y) |> untyped(s) |> map(transpose) |> transpose) :: e.t)
      case _ => Failure(transposeBeforeMapSlide)
    }
    override def toString = "transposeBeforeMapSlide"
  }

  def mapSlideBeforeTranspose: Strategy[Rise] = `*S >> T -> T >> S >> *T`
  case object `*S >> T -> T >> S >> *T` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      Transpose(),
      App(App(Map(), s), y)
      ) if isSplitOrSlide(s) =>
        Success((typed(y) |> transpose >> untyped(s) >> map(transpose)) :: e.t)
      case _ => Failure(mapSlideBeforeTranspose)
    }
    override def toString = "mapSlideBeforeTranspose"
  }

  // transpose + join

  def joinBeforeTranspose: Strategy[Rise] = `J >> T -> *T >> T >> *J`
  case object `J >> T -> *T >> T >> *J` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      Transpose(),
      App(Join(), y)
      ) =>
        Success((typed(y) |> map(transpose) |> transpose |> map(join)) :: e.t)
      case _ => Failure(joinBeforeTranspose)
    }
    override def toString = "joinBeforeTranspose"
  }

  def transposeBeforeMapJoin: Strategy[Rise] = `T >> *J -> *T >> J >> T`
  case object `T >> *J -> *T >> J >> T` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      App(Map(), Join()),
      App(Transpose(), y)
      ) =>
        Success((typed(y) |> map(transpose) |> join |> transpose) :: e.t)
      case _ => Failure(transposeBeforeMapJoin)
    }
    override def toString = "transposeBeforeMapJoin"
  }

  def mapTransposeBeforeJoin: Strategy[Rise] = `*T >> J -> T >> *J >> T`
  case object `*T >> J -> T >> *J >> T` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      Join(),
      App(App(Map(), Transpose()), y)
      ) =>
        Success((typed(y) |> transpose |> map(join) |> transpose) :: e.t)
      case _ => Failure(mapTransposeBeforeJoin)
    }
    override def toString = "mapTransposeBeforeJoin"
  }

  def mapJoinBeforeTranspose: Strategy[Rise] = `*J >> T -> T >> *T >> J`
  case object `*J >> T -> T >> *T >> J` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      Transpose(),
      App(App(Map(), Join()), y)
      ) =>
        Success((typed(y) |> transpose |> map(transpose) |> join) :: e.t)
      case _ => Failure(mapJoinBeforeTranspose)
    }
    override def toString = "mapJoinBeforeTranspose"
  }

  // join + join

  def joinBeforeJoin: Strategy[Rise] = `J >> J -> *J >> J`
  case object `J >> J -> *J >> J` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      Join(),
      App(Join(), y)
      ) =>
        Success((typed(y) |> map(join) >> join) :: e.t)
      case _ => Failure(joinBeforeJoin)
    }
    override def toString = "joinBeforeJoin"
  }

  def mapJoinBeforeJoin: Strategy[Rise] = `*J >> J -> J >> J`
  case object `*J >> J -> J >> J` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      Join(),
      App(App(Map(), Join()), y)
      ) =>
        Success((typed(y) |> join |> join) :: e.t)
      case _ => Failure(mapJoinBeforeJoin)
    }
    override def toString = "mapJoinBeforeJoin"
  }

  // split + slide

  def slideBeforeSplit: Strategy[Rise] = `slide(n)(s) >> split(k) -> slide(k+n-s)(k) >> map(slide(n)(s))`
  case object `slide(n)(s) >> split(k) -> slide(k+n-s)(k) >> map(slide(n)(s))` extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case App(
      DepApp(Split(), k: Nat),
      App(DepApp(DepApp(Slide(), n: Nat), s: Nat), y)
      ) =>
        Success((typed(y) |> slide(k + n - s)(k) |> map(slide(n)(s))) :: e.t)
      case _ => Failure(slideBeforeSplit)
    }
    override def toString = "slideBeforeSplit"
  }


  // nested map + reduce

  // todo simplify
  case object liftReduceOld extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {

      case App(Map(), Lambda(mapVar, App(App(App(rx@(Reduce() | ReduceSeq()), op),
      init :: (dt: DataType)), reduceArg))) :: FunType(ArrayType(size, ArrayType(_,_)), _) =>

        def reduceMap(zippedMapArg : (TDSL[Rise], TDSL[Rise]) => TDSL[Rise], reduceArgFun: TDSL[Rise]): RewriteResult[Rise] = {
          Success((
            untyped(rx)(fun((acc, y) =>
              map(fun(x => app(app(op, fst(x)), snd(x)))) $ zippedMapArg(acc, y)
            ))(generate(fun(IndexType(size) ->: dt)(_ => init))) o reduceArgFun
          ) :: e.t)
        }

        reduceArg match {
          // simple case (see test "lift reduce")
          case x if x == mapVar =>
            reduceMap(
              (acc, y) => zip(acc, y),
              transpose
            )

          // zipped input (see test "MM to MM-LoopMKN")
          case App(App(Zip(), u), v) =>
            val notToBeTransposed = if (mapVar == u) v else u
            reduceMap(
              zippedMapArg = (acc, y) => zip(acc, map(fun(bs => pair(bs, fst(y)))) $ snd(y)),
              reduceArgFun = zip(notToBeTransposed) o transpose
            )
          // input is tile1.tile2.dim.(float,float)
          // dim needs to be reduced -> we need dim.tile1.tile2.(float,float)
          // todo what's the general case? How to (re-)order dimensions here?
          case _ =>
            val result = reduceMap(
              (acc, y) => zip(acc, y),
              transpose o map(transpose)
            )
            result
        }

      case _ => Failure(liftReduce)
    }
    override def toString = "liftReduce"
  }

  case object liftReduce extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {

      case App(Map(), Lambda(mapVar, App(App(App(rx@(Reduce() | ReduceSeq()), op),
      init :: (dt: DataType)), reduceArg))) :: FunType(inputT@ArrayType(size, ArrayType(_,_)), _) =>

      def reduceMap(zippedMapArg : (TDSL[Rise], TDSL[Rise]) => TDSL[Rise], reduceArgFun: TDSL[Rise]): RewriteResult[Rise] = {
          Success((
            untyped(rx)(fun((acc, y) =>
              map(fun(x => app(app(op, fst(x)), snd(x)))) $ zippedMapArg(acc, y)
            ))(generate(fun(IndexType(size) ->: dt)(_ => init))) $ reduceArgFun
          ) :: e.t)
        }

        reduceArg match {
          // simple case (see test "lift reduce")
          // for some reason mapVar might be untyped, hence simply trying `==` fails
          case x if x == mapVar =>
            reduceMap(
              (acc, y) => zip(acc, y),
              transpose
            )
          // zipped input (see test "MM to MM-LoopMKN")
          case App(App(Zip(), u), v) =>
            val notToBeTransposed = if (mapVar == u) v else u
            reduceMap(
              zippedMapArg = (acc, y) =>
                zip(acc, map(fun(bs => pair(bs, fst(y)))) $ snd(y)),
              reduceArgFun = zip(notToBeTransposed) o transpose
            )

          // expression is not in RNF!
          case a@App(_,_) => ???

          case _ =>
            // todo implement recursively
            val reduceArgTransposed = inputT match {
              case ArrayType(_, ArrayType(_, ArrayType(_,ArrayType(_,_)))) => transpose o map(transpose) o map(map(transpose))
              case ArrayType(_, ArrayType(_, ArrayType(_,_))) => transpose o map(transpose)
              case ArrayType(_, ArrayType(_,_)) => transpose
              case _ => ???
            }

            val result = reduceMap(
              (acc, y) => zip(acc, y),
              reduceArgTransposed
            )
            result
        }

      case _ => Failure(liftReduce)
    }
    override def toString = "liftReduce"
  }

  case object liftReduceInReduceOperator extends Strategy[Rise] {
    def apply(e: Rise): RewriteResult[Rise] = e match {
      case op@Lambda(acc_e2348, Lambda(y_e2349,
      App(App(Map(), Lambda(e2350,
      App(App(App(ReduceX(), op2), init), transInput))),
      App(App(zipPrim, inputAcc :: accT), inputY :: yT)) :: resultT)) =>

        // this is the operator for the outer reduce
        val newOuterReduceOp = fun(accT)(acc => fun(yT)(y => // acc :: 32.32.float, y :: 32.32.4.(float,float)
          mapSeq(mapSeq(fun(x => x))) o
            (reduce(
              // inner reduce op
              fun((innerAcc, innerY) =>  // innerAcc :: 32.32.float, innerY :: 32.32.(float,float)
                ((map(map(fun(x => x._1 + (x._2._1 * x._2._2)))) o map(fun(d => zip(d._1, d._2)))) $ zip(innerAcc, innerY)) //)
              ))(
              // init
              acc) o
              //mapSeq(fun(a => mapSeq(fun(x => x)) $ a)) $ acc) o
              transpose o map(transpose)) $ y))

        Success(newOuterReduceOp)

      case op@Lambda(acc_e1504, Lambda(y_e1505,
      App(App(Map(), Lambda(e1506,
      App(App(Lambda(e668, Lambda(e669,
      App(addOp, App(App(App(ReduceX(), op2), init), e669_2))
      )), fst), snd))),
      // unapply zipped branches to get input types
      App(App(zipPrim, inputAcc :: accT), inputY :: yT)) :: resultT)) =>

        // this is the operator for the outer reduce
        val newOuterReduceOp = fun(accT)(acc => fun(yT)(y => // acc :: 32.float, y :: 32.4.(float,float)
          //mapSeq(fun(x => x)) o
          (reduce(
            // inner reduce op
            fun((innerAcc, innerY) =>  // innerAcc :: 32.float, innerY :: 32.(float,float)
              (map(fun(x => x._1 + (x._2._1 * x._2._2))) $ zip(innerAcc, innerY)) //)
            ))(
            // init
            //mapSeq(fun(x => x)) $ acc) o
            acc) o
            transpose) $ y))

        Success(newOuterReduceOp)
      case _ => Failure(liftReduceInReduceOperator)
    }
  }
}
