import org.scalatest.FlatSpec
import scala.util.Try
import scala.io.Source
import scala.collection.mutable.ListBuffer

class EquivalenceTestSpec extends FlatSpec {

    val path = "testcases/txt/"

    def getTestCase(file: String, opt_file: String, testnum: Int): (Boolean, Expr, Expr, String) = {
        val inputfile1 = Source.fromFile(path + file)  
        val inputfilecontent1   = inputfile1.mkString
        val inputfile2 = Source.fromFile(path + opt_file)  
        val inputfilecontent2   = inputfile2.mkString
        val rawFile = ScalaParser.parseStatement(inputfilecontent1)
        val optFile = ScalaParser.parseStatement(inputfilecontent2)
        ScalaInterpreter.cleanup
        rawFile match {
            case Some(text1) =>
                ScalaInterpreter.interpretStmt(text1)
                val expressions1 = ScalaInterpreter.outputVarMap
                ScalaInterpreter.cleanup
                optFile match {
                    case Some(text2) =>  
                        ScalaInterpreter.interpretStmt(text2) 
                        val expressions2 = ScalaInterpreter.outputVarMap
                        var testcases = new Array[(Expr, Expr, String)](expressions1.size)
                        var index = 0
                        expressions1.foreach {
                            case(output, exp) => 
                                val eq_exp = expressions2.get(output)
                                eq_exp match {
                                    case Some(value) => 
                                        val tup = (exp, value, output)
                                        testcases(index) = tup 
                                        index += 1
                                    case None => 
                                        assert(false, "Optimized expression not found")
                                }  
                        }
                        testcases.sortBy(_._3)
                        (true, testcases(testnum)._1, testcases(testnum)._2, testcases(testnum)._3)

                    case None => assert(false, "Parsing Error"); (false, BoolLit(false), BoolLit(false), "Invalid")
                }
            case None => assert(false, "Parse error"); (false, BoolLit(false), BoolLit(false), "Invalid")

        }                                         
    }

    //Some Visible TestCases


    "Test 1 - " should "run successfully" in {
        info("Testfile -> apex4")
        val testcase = getTestCase("apex4.txt", "apex4_opt.txt", 0)
        testcase match {
            case (success, exp, optimized_exp, testnum) =>
                if(success) {
                    info("Checking -> " + testnum.toString)
                    assert(!Evaluation.areEquivalent(exp, Not(optimized_exp)), "Eqivalent Check Failed")
                    assert(Evaluation.areEquivalent(exp, optimized_exp), "Eqivalent Check Failed")
                }
                else {
                    assert(false, "Testcase Error")
                }
        }
    }


    "Test 2 - " should "run successfully" in {
        info("Testfile -> apex4")
        val testcase = getTestCase("apex4.txt", "apex4_opt.txt", 1)
        testcase match {
            case (success, exp, optimized_exp, testnum) =>
                if(success) {
                    info("Checking -> " + testnum.toString)
                    assert(!Evaluation.areEquivalent(exp, Not(optimized_exp)), "Eqivalent Check Failed")
                    assert(Evaluation.areEquivalent(exp, optimized_exp), "Eqivalent Check Failed")
                }
                else {
                    assert(false, "Testcase Error")
                }
        }
    }

    //Test 3,4

    "Test 5 - " should "run successfully" in {
        info("Testfile -> apex4")
        val testcase = getTestCase("apex4.txt", "apex4_opt.txt", 4)
        testcase match {
            case (success, exp, optimized_exp, testnum) =>
                if(success) {
                    info("Checking -> " + testnum.toString)
                    assert(!Evaluation.areEquivalent(exp, Not(optimized_exp)), "Eqivalent Check Failed")
                    assert(Evaluation.areEquivalent(exp, optimized_exp), "Eqivalent Check Failed")
                }
                else {
                    assert(false, "Testcase Error")
                }
        }
    }

    //Test 6 hidden

    "Test 7 - " should "run successfully" in {
        info("Testfile -> apex4")
        val testcase = getTestCase("apex4.txt", "apex4_opt.txt", 6)
        testcase match {
            case (success, exp, optimized_exp, testnum) =>
                if(success) {
                    info("Checking -> " + testnum.toString)
                    assert(!Evaluation.areEquivalent(exp, Not(optimized_exp)), "Eqivalent Check Failed")
                    assert(Evaluation.areEquivalent(exp, optimized_exp), "Eqivalent Check Failed")
                }
                else {
                    assert(false, "Testcase Error")
                }
        }
    }


    "Test 8 - " should "run successfully" in {
        info("Testfile -> apex4")
        val testcase = getTestCase("apex4.txt", "apex4_opt.txt", 7)
        testcase match {
            case (success, exp, optimized_exp, testnum) =>
                if(success) {
                    info("Checking -> " + testnum.toString)
                    assert(!Evaluation.areEquivalent(exp, Not(optimized_exp)), "Eqivalent Check Failed")
                    assert(Evaluation.areEquivalent(exp, optimized_exp), "Eqivalent Check Failed")
                }
                else {
                    assert(false, "Testcase Error")
                }
        }
    }


}