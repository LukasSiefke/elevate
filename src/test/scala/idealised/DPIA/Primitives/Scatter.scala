package idealised.DPIA.Primitives

import idealised.OpenCL.SurfaceLanguage.DSL.reorderWithStridePhrase
import idealised.SurfaceLanguage.DSL._
import idealised.SurfaceLanguage.NatIdentifier
import idealised.SurfaceLanguage.Types._
import idealised.util.SyntaxChecker
import lift.arithmetic._

class Scatter extends idealised.util.Tests {

  test("Simple scatter example should generate syntactic valid C code with two one loops") {
    val slideExample =
      nFun(n =>
        fun(ArrayType(n, float))(xs =>
          xs :>> mapSeq(fun(x => x)) :>> scatter(reorderWithStridePhrase(128)) ))

    val p = idealised.C.ProgramGenerator.makeCode(TypeInference(slideExample, Map()).toPhrase)
    val code = p.code
    SyntaxChecker(code)
    println(code)

    "for".r.findAllIn(code).length shouldBe 1
  }

  ignore ("Simple 2D scatter example should generate syntactic valid C code with two two loops") {
    val slideExample =
      nFun(n => nFun(m =>
        fun(ArrayType(SizeVar("N"), ArrayType(SizeVar("M"), float)))(xs =>
          xs :>> mapSeq(mapSeq(fun(x => x))) :>> mapOut(scatter(reorderWithStridePhrase(128))) )))

    val p = idealised.C.ProgramGenerator.makeCode(TypeInference(slideExample, Map()).toPhrase)
    val code = p.code
    SyntaxChecker(code)
    println(code)

    "for".r.findAllIn(code).length shouldBe 2
  }

}