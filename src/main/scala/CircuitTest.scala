 

import scala.util.Try
import scala.io.Source

object CircuitTest
{

    def and(args: Expr*): Expr = And(args.toList)
    def or(args: Expr*): Expr = Or(args.toList)
    def not(arg: Expr): Expr = Not(arg)
    def var_(name: String) : Variable = Variable(name)
    def lit(value: Boolean): Expr = BoolLit(value)

    def a = var_("a")
    def b = var_("b")
    def c = var_("c")
    def d = var_("d")
    def e = var_("e")
    def f = var_("f")


    //This is just a sample and not part of the actual testcases. 
    def sampleTest = 
    {
        val exp = and(and(a,b), or(c,d))
        val modifiedExp1 = and(or(a,b), or(c,d))
        val modifiedExp2 = and(and(a,b), or(c,d))
        val modifiedExp3 = or(and(a,b), or(c,d))
        def evaluateWrapper1(m: Map[Variable, Boolean]) = Evaluation.evaluate(modifiedExp1, m)
        def evaluateWrapper2(m: Map[Variable, Boolean]) = Evaluation.evaluate(modifiedExp2, m)
        def evaluateWrapper3(m: Map[Variable, Boolean]) = Evaluation.evaluate(modifiedExp3, m)


        val orig = Not(and(a, and(a,b)))
        val mod =  Not(and(a ,and(a,b)))
        def evaluateWrap(m: Map[Variable, Boolean]) = Evaluation.evaluate(mod, m)

        println("result" + Circuit.checkEquivalenceOfCircuits(orig, evaluateWrap))
        assert(!Circuit.checkEquivalenceOfCircuits(exp, evaluateWrapper1))
        assert(Circuit.checkEquivalenceOfCircuits(exp, evaluateWrapper2))
        assert(!Circuit.checkEquivalenceOfCircuits(exp, evaluateWrapper3))
        assert(Circuit.checkEquivalenceOfCircuits(exp, evaluateWrapper2))
    }

    def main(array: Array[String])={
        sampleTest
    }
}
