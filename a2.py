# -*- coding: utf-8 -*-
from utils import (remove_all, unique, first, argmax, probability, isnumber,
                   issequence, Expr, expr, subexpressions, extend)

from logic import PropKB, pl_resolution, FolKB

from planning import PlanningProblem, ForwardPlan, Action

from search import astar_search

import re

""" A2 Part A

    giveFeedback is a function that reads in a student state and returns a feedback message using propositional logic and proof by resolution. The rules
    for how to decide which message to return are given in the assignment description.

    studentState:   a String representing a conjunction of five possible symbols: CorrectAnswer, NewSkill, MasteredSkill, CorrectStreak, IncorrectStreak
                    For example, you could call giveFeedback('CorrectAnswer') or giveFeedback('MessageasteredSkill & CorrectStreak')

    feedbackMessage:a String representing one of eight feedback messages (M1 through M8 below).

    Feel free to refactor the code to move M1 through M8 into a class, but the function call and return values should remain as specified below for our grading.
"""

message_arr = ["Message1", "Message2", "Message3", "Message4", "Message5", "Message6", "Message7", "Message8"]
# This specifies whether the student’s most recent answer was correct
CorrectAnswer=expr("CorrectAnswer")
# This specifies whether this skill related to the student’s most recent answer is new to the student
# (the student has not yet seen a problem with that skill)
NewSkill=expr("NewSkill")
# This specifies whether the skill related to the student’s most recent answer has been mastered by the student
MasteredSkill=expr("MasteredSkill")
# This specifies whether the student’s last three answers were correct
CorrectStreak=expr("CorrectStreak")
# This specifies whether the student’s last three answers were incorrect
IncorrectStreak=expr("IncorrectStreak")
expression_lookup = {"CorrectAnswer": CorrectAnswer, "NewSkill": NewSkill, "MasteredSkill": MasteredSkill, "CorrectStreak": CorrectStreak, "IncorrectStreak": IncorrectStreak}

message_lookup = {}
message_lookup["Message1"] = "Correct. Keep up the good work!"
message_lookup["Message2"] = "Correct. I think you're getting it!"
message_lookup["Message3"] = "Correct. After this problem we can switch to a new problem."
message_lookup["Message4"] = "Incorrect. Keep trying and I'm sure you'll get it!"
message_lookup["Message5"] = "Incorrect. After this problem, we can switch to a new activity."
message_lookup["Message6"] = 'Incorrect. The following is the correct answer to the problem.'
message_lookup["Message7"] = 'Correct.'
message_lookup["Message8"] = 'Incorrect.'

def giveFeedback(studentState):
    feedback_kb = PropKB()
    # The implementation of .tell() is found in logic.py
    # def to_cnf(s): -> This takes in the string passed into .tell()
    # def eliminate_implications(s): -> This will parse the expressions and logic symbols
    # CorrectAnswer => (Message1 v Message2 v Message3 v Message7)
    feedback_kb.tell('CorrectAnswer ==> (Message1 | Message2 | Message3 | Message7)')
    # ~CorrectAnswer => (Message4 v Message5 v Message6 v Message8)
    feedback_kb.tell('~CorrectAnswer ==> (Message4 | Message5 | Message6 | Message8)')
    # (MasteredSkill & IncorrectAnswer) v (MasteredSkill & CorrectStreak) => IsBored
    feedback_kb.tell('(MasteredSkill & ~CorrectAnswer) | (MasteredSkill & CorrectStreak) ==> IsBored')
    # NewSkill v IncorrectStreak => Message6
    feedback_kb.tell('NewSkill | IncorrectStreak ==> Message6')
    # (IncorrectStreak & CorrectAnswer) v (NewSkill & CorrectStreak) => NeedsEncouragement
    feedback_kb.tell('(IncorrectStreak & CorrectAnswer) | (NewSkill & CorrectStreak) ==> NeedsEncouragement')
    # NeedsEncouragement => Message2 v Message4
    feedback_kb.tell('NeedsEncouragement ==> Message2 | Message4')
    # IsBored => Message3 v Message5
    feedback_kb.tell('IsBored ==> Message3 | Message5')
    # (NewSkill & CorrectAnswer) v CorrectStreak => Message1
    feedback_kb.tell('(NewSkill & CorrectAnswer) | CorrectStreak ==> Message1')

    feedback_kb.tell(expr(studentState))
    message = "NONE FOUND"
    # Look for the correct message
    for m in message_arr:
        # print("Finding if " + m + " is TRUE in the KB")
        foundMessage = pl_resolution(feedback_kb, expr(m))
        if foundMessage:
            return message_lookup[m]
        else:
            feedback_kb.tell(expr("~" + m))

def test_give_feedback():
    print("Testing giveFeedback()...");

    print("giveFeedback('CorrectAnswer & CorrectStreak') returns " + giveFeedback("CorrectAnswer & CorrectStreak") + " (should be " + message_lookup["Message1"] + ")")
    print("giveFeedback('CorrectAnswer & IncorrectStreak') returns " + giveFeedback('CorrectAnswer & IncorrectStreak') + " (should be " + message_lookup["Message2"] + ")")
    print("giveFeedback('CorrectAnswer') returns " + giveFeedback('CorrectAnswer') + " (should be " + message_lookup["Message7"] + ")")

# test_give_feedback()

""" A2 Part B

Then, implement a solveEquation function that executes the planning (30 points).
solveEquation takes as a single parameter a string representing the equation
to be solved. Your system should use your first-order logic representation and
forward planning, and return a list of actions to execute based on the problem
description. For example, the call solveEquation(‘3x-2=6’) should return:
[‘add 2’, ‘combine RHS constant terms’, ‘divide 3’]. You can assume that
terms like +2 and -2 automatically cancel out, and don’t require an action.
Full marks will be given if the system successfully uses first-order logic and
forward planning to return the most efficient solution to the problem.

    solveEquation is a function that converts a string representation of an equation to a first-order logic representation, and then
    uses a forward planning algorithm to solve the equation.

    equation:   a String representing the equation to be solved. "x=3", "-3x=6", "3x-2=6", "4+3x=6x-7" are all possible Strings.
                For example, you could call solveEquation('x=6') or solveEquation('-3x=6')

    plan:   return a list of Strings, where each String is a step in the plan. The Strings should reference the core actions described in the
            Task Domain part of the assignment description.

"""
def parse_equation(equation):
    # Counts will be used for goal generation special cases (already solved)
    counts = {
        "Const": {
            "Left": [],
            "Right": []
        },
        "Var": {
            "Left": [],
            "Right": []
        }
    }
    # This will be an array of strings that will be added to the KB
    statements = [];
    side = "Left"
    # Read the equation right to left
    num = 0
    skips = 0
    for char in equation:
        # Some of these look ahead in the equation, for loop must catch up
        if skips > 0:
            skips -= 1
            num += 1
            continue

        if char == "x":
            statements.append(side + "Var(1)")
            counts["Var"][side].append(1)
        elif char == "-":
            # If the next character is an x
            if (num + 1) < len(equation) and equation[num + 1] == "x":
                statements.append(side + "Var(" + char + "1)") # -x
                counts["Var"][side].append(-1)
                skips = 1
            # In this case, the next character MUST be some number followed by an x
            elif (num + 2) < len(equation) and isNum(equation[num + 1]) and equation[num + 2] == "x":
                statements.append(side + "Var(" + char + equation[num + 1] + ")")
                counts["Var"][side].append(int(char + equation[num + 1]))
                skips = 2
            # The only other possibility is that there is a negative constant
            elif (num + 1) < len(equation):
                # Add this to counts,
                statements.append(side + "Const(" + char + equation[num + 1] + ")")
                counts["Const"][side].append(int(char + equation[num + 1]))
                skips = 1
        elif char == "=":
            side = "Right"
        # The current character is a number 1-9
        elif isNum(char):
            if (num + 1) < len(equation) and equation[num + 1] == "x":
                statements.append(side + "Var(" + char + ")")
                counts["Var"][side].append(int(char))
                skips = 1
            # If the next character isn't an x, this must be a single constant
            else:
                statements.append(side + "Const(" + char + ")")
                counts["Const"][side].append(int(char))
        elif char == "+":
            pass # We actually don't care about if it's positive
        # Keep track of the current character in the string
        num += 1
    return statements, counts

def print_action(name, precond, effect):
    print("\t\t" + name)
    print("\t\t\tPre:  " + precond + "\n\t\t\tPost: " + effect)

def isNum(character):
    numbers = ["1", "2", "3", "4", "5", "6", "7", "8", "9"]
    if character in numbers:
        return True
    return False

def solveEquation(equation, debug=False):
    """
    HOW TO SOLVE EQUATIONS:
    COMBINE
    1.  Convert the input string: x=3+3
    2.  Your initial becomes the following:
        - LeftVar(1)
        - RightConst(3)
        - RightConst(3)
    3.  The actions you generate are the following:
        - CombineRightConst()
            Pre:  RightConst(a) & RightConst(b)
            Post: ~RightConst(a) & ~RightConst(b) & RightConst()
    4.  For the goal, make sure you have the following:
        - BASE_CLAUSE (LeftVar(1) & RightConst(x)) &
        - ~RightConst(3) & ~RightConst(3)
        * Basically, the negation of everything you started with, plus the last line ALWAYS

    ADD
    1.  Convert the following input string: x+3=5
    2.  Your initial becomes the following:
        - LeftVar(1)
        - LeftConst(3)
        - RightConst(5)
    3.  The actions you generate are the following:
        - AddLeftConstant(a)
            Pre:  LeftConst(a)
            Post: ~LeftConst(a) & RightConst(a)
    4.  For the goal, make sure you have the following:
        - BASE_CLAUSE (LeftVar(1) & RightConst(x)) &
        # SUBTRACT RULES
        - ~LeftConst(3)
        # COMBINE RULES
        - ~RightConst(3) & ~RightConst(5) & RightConst(x)

    DIVIDE
    1.  Convert the following input string: 3x-2=6
    2.  Initial Variables:
        - LeftVar(3)
        - LeftConst(-2)
        - RightConst(6)
    3.  The actions you generate are the following:
        - DivideLeftVar(a)
            Pre:  LeftVar(a) & RightConst(x)      This forces it to go after right is finished
            Post: LeftVar(1) & ~LeftVar(a) & DivideLeftVar(a)
    4.  For the goal, don't add anything because a LeftVar(1) is already mandated
    """
    statements, counts = parse_equation(equation)
    # This should be loaded with the state of the equation
    # Ex: LeftVar(3) & LeftConst(-2) & RightConst(6)
    init_string = " & "
    init_string = init_string.join(statements)
    if debug:
        print("\tCounts: " + str(counts))
        print("\tInit: " + init_string)

    # =============== CREATE ALL ACTIONS =====================
    extra_goals = [] # These are all the extra goals we generate from special cases in actions
    if debug:
        print("\tActions: ")
    actions_arr = []
    for type in ["Const", "Var"]:
        for side in ["Left", "Right"]:
            # The combining method
            side_type = side + type
            name = "Combine" + side_type + "(a, b)"
            precond = side_type + "(a) & " + side_type + "(b)"
            effect = side_type + "(x) & ~" + side_type + "(a) & ~" + side_type + "(b)" + " & " + name
            new_action = Action(name, precond=precond, effect=effect)
            if debug:
                print_action(name, precond, effect)
            actions_arr.append(new_action)

            # Add method
            if side_type == "LeftConst" or side_type == "RightVar":
                # We don't need to add right constants, they are supposed to be on the right
                # Don't need to add left variables, supposed to be on the left
                opposite_side = "Left"
                if side == "Left":
                    opposite_side = "Right"

                name = "Add" + side_type + "(a)"
                precond = side_type + "(a)"
                effect = opposite_side + type + "(a) & ~" + side_type + "(a)" + " & " + name
                if side_type == "RightVar" and len(counts["Var"]["Left"]) == 1 and len(counts["Var"]["Right"]) == 1:
                    # Check if there is a variable on the left, in which case mandate we COMBINE
                    # Ex: 4x=3x+2
                    extra_goals.append(" & ~" + opposite_side + type + "(" + str(counts["Var"]["Right"][0]) + ")")

                new_action = Action(name, precond=precond, effect=effect)
                if debug:
                    print_action(name, precond, effect)
                actions_arr.append(new_action)

            # Divide method
            """
            5x=x+3

            """
            if side_type == "LeftVar": # You can only divide VARS once they are on the left
                name = "Divide" + side_type + "(a)"
                precond = side_type + "(a)"
                effect = side_type + "(1) & ~" + side_type + "(a) & " + name # This is the goal state
                # Special case for 4x=x, x-x=3x, or any scenario when there are no constants
                if counts["Const"]["Right"] + counts["Const"]["Left"] == 0:
                    effect += " & " + "RightConst(x)"

                new_action = Action(name, precond=precond, effect=effect)
                if debug:
                    print_action(name, precond, effect)
                actions_arr.append(new_action)

    # =============== CREATE ALL GOALS =====================

    goals_arr = [] # ALWAYS in the form x=const

    if len(counts["Var"]["Left"]) + len(counts["Var"]["Right"]) > 1:
        goals_arr.append("LeftVar(x)")
    else:
        goals_arr.append("LeftVar(1)")

    if len(counts["Const"]["Left"]) + len(counts["Const"]["Right"]) > 1:
        goals_arr.append("RightConst(x)")
    elif len(counts["Const"]["Left"]) == 1 and len(counts["Const"]["Right"]) == 0:
        goals_arr.append("RightConst(" + str(counts["Const"]["Left"][0]) + ")")
    elif len(counts["Const"]["Left"]) == 0 and len(counts["Const"]["Right"]) == 1:
        goals_arr.append("RightConst(" + str(counts["Const"]["Right"][0]) + ")")

    found_single_left_var = False
    for statement in statements:
        # ============ COMBINE GOALS ==============
        # We don't want to negate something already in out goal, but we also ONLY want one
        if not found_single_left_var and statement == "LeftVar(1)":
            found_single_left_var = True
            continue # We would not want to mandate this ONE is negated
        if "RightConst" in statement and len(counts["Const"]["Right"]) == 1:
            continue # Don't negate it for combination if it's the only one

        goals_arr.append("~" + statement)

        # ============ ADD GOALS ==============
        if "RightVar" in statement:
            goals_arr.append("~" + statement) # Force to move right var

        elif "LeftConst" in statement:
            goals_arr.append("~" + statement)

        # ============ DIVIDE GOALS ==============

    goal_string = " & "
    goal_string = goal_string.join(goals_arr)

    # ============ DIVIDE GOALS ==============

    # We MUST combine these, not divide them all to one
    if len(counts["Var"]["Left"]) == 1 and len(counts["Var"]["Right"]) == 1:
        extra_goals.append(" & CombineLeftVar(" + str(counts["Var"]["Left"][0]) + ", " + str(counts["Var"]["Right"][0]) + ")")

    if debug:
        print("\tGoals: " + str(goal_string))
        print("\tExtra Goals: " + str(extra_goals))

    for extra_goal in extra_goals:
        goal_string += extra_goal

    equation_plan = PlanningProblem(
        initial=init_string,
        goals=goal_string,
        # Checkout class Action: -> Located in planning.py
        # Line 195 in the Action class has a convert() function, where we can resolve these additions
        actions=actions_arr
    )
    print("\t==== SOLVING ====")
    action_plan = ForwardPlan(equation_plan)
    steps = []
    plans = astar_search(action_plan)
    if debug:
        print("\tPlans:")
    if plans == None:
        # Check if we actually need to solve the equation, BASE CASE
        if counts["Var"]["Left"] == 1 and counts["Var"]["Right"] == 0 and counts["Const"]["Left"] == 0 and counts["Const"]["Right"] == 1:
            return [] # This does NOT need to be solved
        if counts["Var"]["Left"] == 0 and counts["Var"]["Right"] == 1 and counts["Const"]["Left"] == 1 and counts["Const"]["Right"] == 0:
            return [] # This does NOT need to be solved
        return plans

    # Determine the final var value after combinations, used to determine if COMBINE is POS/NEG
    final_var_value = 0
    final_var_sign = "negative"
    for varVal in counts["Var"]["Left"]:
        final_var_value += varVal
    for varVal in counts["Var"]["Right"]:
        final_var_value -= varVal
    if final_var_value >= 0:
        final_var_sign = "positive"

    plans = str(plans.state)
    plans = plans[1:len(plans) - 1]
    divide_step = ""
    for plan in plans.split(" & "):
        if debug:
            print("\t\t" + plan)
        # Combine messages
        if "CombineRightConst" in plan:
            steps.append("combine RHS constant terms")
        elif "CombineLeftConst" in plan:
            steps.append("combine LHS constant terms")
        elif "CombineLeftVar" in plan:
            steps.append("combine LHS variable terms and get " + final_var_sign)
        elif "CombineRightVar" in plan:
            steps.append("combine RHS variable terms and get " + final_var_sign)
        elif "DivideLeftVar" in plan:
            val = plan[plan.index("(") + 1:len(plan) - 1]
            divide_step = "divide " + val
        # Add messages
        elif "Add" in plan:
            val = int(plan[plan.index("(") + 1:len(plan) - 1])
            operation = "Add"
            if val > 0:
                val = -val
            #if "Var" in plan:
            step = operation + " " + str(val)
            if "Var" in plan:
                step += "x"
            steps.insert(0, step)

    if divide_step != "" and "1" not in divide_step:
        steps.append(divide_step)

    return steps

def testSolveEquation():
    initial_test_cases = ["x=3", "3=x"]
    combine_test_cases = ["x=4+3", "x+2x=3+4"]
    add_test_cases = ["x+3=2+1", "x-1=5", "3+x=5", "x+4=-4-2"]
    divide_cases = ["3x=6+2", "x=4x", "4+4x=3x-7", "7x=3x-3", "2x-x=3", "2x+2=4+6"]
    test_suite = [initial_test_cases, combine_test_cases, add_test_cases, divide_cases]
    for test_cases in test_suite:
        for test_case in test_cases:
            print("\nRunning solveEquation('" + test_case + "')...");
            debug_mode = False
            result = solveEquation(test_case, debug_mode)
            if result == None:
                print("\tRESULT:\tNo results found!")
            else:
                print("\tRESULT:\t" + str(result))

# testSolveEquation()

""" A2 Part C

predictSuccess is a function that takes in a list of skills students have and an equation to be solved, and returns the skills
students need but do not currently have in order to solve the skill. For example, if students are solving the problem 3x+2=8, and have S7 and S8,
they would still need S4 and S5 to solve the problem.

current_skills: A list of skills students currently have, represented by S1 through S9 (described in the assignment description)

equation:   a String representing the equation to be solved. "x=3", "-3x=6", "3x-2=6", "4+3x=6x-7" are all possible Strings.
            For example, you could call solveEquation('x=6') or solveEquation('-3x=6')

missing_skills: A list of skills students need to solve the problem, represented by S1 through S9.

S1: add a positive variable term to both sides (e.g., add 3x to both sides)
S2: add a negative variable term to both sides (e.g., add -3x to both sides)
S3: add a positive constant term to both sides (e.g., add +3 to both sides)
S4: add a negative constant term from both sides  (e.g., add -3 to both sides)
S5: divide both sides by a positive constant (e.g., divide by 3)
S6: divide both sides by a negative constant (e.g., divide by -3)
S7: combine two variable terms on a side to get a positive number (e.g., combine 3x+6x to make 9x)
S8: combine two variable terms on a side to get a negative number (e.g., combine 3x-6x to make -9x)
S9: combine two constant terms (e.g., combine 3-6 to make -3)
"""

def predictSuccess(current_skills, equation, debug=False):
    skills_needed = []
    statements, counts = parse_equation(equation)
    print("Predicting success on " + equation)
    print("\tSkills: " + str(current_skills))
    if debug:
        print("\tStatements: " + str(statements))

    skills_kb = FolKB()
    for statement in statements:
        skills_kb.tell(expr(statement))

    # Skill 9 - combine two constant terms
    if len(counts["Const"]["Left"]) + len(counts["Const"]["Right"]) > 1:
        skills_kb.tell(expr("LeftConst(a) & RightConst(b) ==> Skill9(a, b)"))
        skills_kb.tell(expr("RightConst(a) & RightConst(b) ==> Skill9(a, b)"))

    # Skill 8 - combine two variable terms on a side to get a negative number
    # Skill 7 - combine two variable terms on a side to get a positive number
    if len(counts["Var"]["Left"]) + len(counts["Var"]["Right"]) > 1:
        if len(counts["Var"]["Left"]) == 1 and len(counts["Var"]["Right"]) == 1: # Ex: 2x=4x+1
            if counts["Var"]["Left"][0] - counts["Var"]["Right"][0] < 0:
                skills_kb.tell(expr("LeftVar(a) & RightVar(b) ==> Skill8(a, b)"))
            else:
                skills_kb.tell(expr("LeftVar(a) & RightVar(b) ==> Skill7(a, b)"))
        elif len(counts["Var"]["Left"]) >= 2:
            if counts["Var"]["Left"][0] + counts["Var"]["Left"][1] < 0: # Ex: 4x-6x=4
                skills_kb.tell(expr("LeftVar(a) & LeftVar(b) ==> Skill8(a, b)"))
            else:
                skills_kb.tell(expr("LeftVar(a) & LeftVar(b) ==> Skill7(a, b)"))
        elif len(counts["Var"]["Right"]) >= 2:
            if counts["Var"]["Right"][0] + counts["Var"]["Right"][1] < 0: # Ex: 4=4x-6x
                skills_kb.tell(expr("RightVar(a) & RightVar(b) ==> Skill8(a, b)"))
            else:
                skills_kb.tell(expr("RightVar(a) & RightVar(b) ==> Skill7(a, b)"))

    # Skill 6 - divide both sides by a negative constant
    # Skill 5 - divide both sides by a positive constant
    final_var_value = 0
    for varVal in counts["Var"]["Left"]:
        final_var_value += varVal
    for varVal in counts["Var"]["Right"]:
        final_var_value -= varVal
    if debug:
        print("\tFinal var value: " + str(final_var_value))
    if final_var_value < 0:
        skills_kb.tell(expr("LeftVar(a) ==> Skill6(a)"))
        skills_kb.tell(expr("RightVar(a) ==> Skill6(a)"))
    elif final_var_value == 1:
        pass
    else:
        skills_kb.tell(expr("LeftVar(a) ==> Skill5(a)"))
        skills_kb.tell(expr("RightVar(a) ==> Skill5(a)"))

    # Skill 4 - add a negative constant term from both sides
    # Skill 3 - add a positive constant term to both sides
    if len(counts["Const"]["Left"]) > 0:
        final_left_value = 0
        for constVal in counts["Const"]["Left"]:
            final_left_value += constVal
        if final_left_value < 0:
            skills_kb.tell(expr("LeftConst(a) ==> Skill3(a)"))
        else:
            skills_kb.tell(expr("LeftConst(a) ==> Skill4(a)"))

    skills = ["Skill9", "Skill8", "Skill7", "Skill6", "Skill5", "Skill4", "Skill3", "Skill2", "Skill1"]
    two_param_skills = ["Skill9", "Skill8", "Skill7"]

    # Skill 2 - add a negative variable term to both sides
    # Skill 1 - add a positive variable term to both sides
    if len(counts["Var"]["Right"]) > 0:
        final_right_value = 0
        for varVal in counts["Var"]["Right"]:
            final_right_value += varVal
        if final_right_value < 0:
            skills_kb.tell(expr("RightVar(a) ==> Skill1(a)"))
        else:
            skills_kb.tell(expr("RightVar(a) ==> Skill2(a)"))

    if debug:
        print("\tAsk KB:")
    for skill in skills:
        if skill in two_param_skills and skills_kb.ask(expr(skill + '(a, b)')):
            skills_needed.append(skill[0] + skill[-1])
            if debug:
                print("\t\t" + skill + " ==> NEEDED")
        elif skills_kb.ask(expr(skill + '(a)')):
            skills_needed.append(skill[0] + skill[-1])
            if debug:
                print("\t\t" + skill + " ==> NEEDED")

    missing_skills = []
    for skill in skills_needed:
        if skill not in current_skills: # If we don't know the skill yet
            missing_skills.append(skill)
    return missing_skills

def test_predict_success():
    print("\tMissing: " + str(predictSuccess(["S1"], "-7x-5=4-2x", debug=False))) # Skill 1, 3, 6, 8, 9
    print("\tMissing: " + str(predictSuccess(["S1", "S4", "S5"], "x=4", debug=False))) # Special case, no skills
    print("\tMissing: " + str(predictSuccess(["S1", "S4", "S5"], "x=4+7", debug=False))) # Skill 9 only
    print("\tMissing: " + str(predictSuccess(["S1", "S6"], "x-3x=4x+7", debug=False))) # Skill 2, 6, 8
    print("\tMissing: " + str(predictSuccess([], "x+2=4", debug=False))) # Skill 4, 9
    print("\tMissing: " + str(predictSuccess(["S8"], "6x+2x=4", debug=False))) # Skill 5, 7

# test_predict_success()

""" A2 Part D

    stepThroughProblem is a function that takes a problem, a student action, and a list of current student skills, and returns
    a list containing a feedback message to the student and their updated list of skills.

    equation: a String representing the equation to be solved. "x=3", "-3x=6", "3x-2=6", "4+3x=6x-7" are all possible Strings.

    action: an action in the task domain. For example: 'add 2', 'combine RHS constant terms', 'divide 3'

    current_skills: A list of skills students currently have, represented by S1 through S9 (described in the assignment description)

    feedback_message: A feedback message chosen correctly from M1-M9.

    updated_skills: A list of skills students have after executing the action.

"""

# This specifies whether the student’s most recent answer was correct
# CorrectAnswer=expr("CorrectAnswer")
# This specifies whether this skill related to the student’s most recent answer is new to the student
# (the student has not yet seen a problem with that skill)
# NewSkill=expr("NewSkill")
# This specifies whether the skill related to the student’s most recent answer has been mastered by the student
# MasteredSkill=expr("MasteredSkill")
# This specifies whether the student’s last three answers were correct
# CorrectStreak=expr("CorrectStreak")
# This specifies whether the student’s last three answers were incorrect
# IncorrectStreak=expr("IncorrectStreak")
correct_streak = 0
incorrect_streak = 0

def stepThroughProblem(equation, action, current_skills, debug=False):
    global correct_streak
    global incorrect_streak
    correct_actions = solveEquation(equation, debug=False)
    feedback_input = [] # Used as input for giveFeedback, added to KB
    new_skill = action_to_skill(action) # Used to detect NewSkill and MasteredSkill, also to update the current_skills
    print("stepThroughProblem()...")
    if debug:
        print("\tEquation: " + equation)
        print("\tCorrect actions: " + str(correct_actions))
        print("\tAction input: '" + action + "'")
        print("\tCurrent skills: " + str(current_skills))

    # Check if the answer is correct...
    is_correct = False
    if correct_actions[0].lower() == action.lower():
        if debug:
            print("\tResult: Correct action! '" + correct_actions[0].lower() + "' == '" + action.lower() + "'")
            print("\t\tAdding CorrectAnswer to the KB...")
        feedback_input.append("CorrectAnswer")
        correct_streak += 1
        incorrect_streak = 0 # reset incorrect streak...

        if new_skill not in current_skills:
            if debug:
                print("\t\tAdding NewSkill to the KB...")
            feedback_input.append("NewSkill")
        else: # The skill was already in the KB
            if debug:
                print("\t\tAdding MasteredSkill to the KB...")
            feedback_input.append("MasteredSkill")

        if correct_streak >= 3:
            if debug:
                print("\t\tAdding CorrectStreak to the KB...")
            correct_streak = 0
            feedback_input.append("CorrectStreak")
        is_correct = True
    else:
        if debug:
            print("\tResult: Incorrect action. '" + correct_actions[0].lower() + "' != '" + action.lower() + "'")
            print("\t\tAdding ~CorrectAnswer to the KB...")
        feedback_input.append("~CorrectAnswer")
        incorrect_streak += 1
        correct_streak = 0 # reset correct streak...

        if incorrect_streak >= 3:
            incorrect_streak = 0
            feedback_input.append("IncorrectStreak")
            if debug:
                print("\t\tAdding IncorrectStreak to the KB...")

    # Generate feedback message from the student state generated in feedback_input
    feedback_input_string = " & ".join(feedback_input)
    if debug:
        print("\tFeedback input: " + feedback_input_string)
    print("\tGenerating feedback message...")
    feedback_message = giveFeedback(feedback_input_string)

    # Return feedback and CURRENT skills if incorrect last answer...
    if not is_correct:
        return [feedback_message, current_skills]

    # At this point, they are correct and we need to update their skills based on the action
    if debug:
        print("\tNew skill: " + new_skill)
    updated_skills = current_skills
    updated_skills.append(new_skill)
    return [feedback_message, updated_skills]

def action_to_skill(action):
    action = action.lower()
    # Skill 9 - combine two constant terms
    if "combine" in action and "constant" in action:
        return "S9"

    # Skill 8 - combine two variable terms on a side to get a negative number
    # Skill 7 - combine two variable terms on a side to get a positive number
    if "combine" in action and "variable" in action:
        return "S7"
        # IDK how to detect, based on an action, if the variables will be negative

    # Skill 6 - divide both sides by a negative constant
    # Skill 5 - divide both sides by a positive constant
    if "-" in action and "divide" in action:
        return "S6"
    elif "divide" in action:
        return "S5"

    # Skill 4 - add a negative constant term from both sides
    # Skill 3 - add a positive constant term to both sides
    if "add" in action and "-" in action and "x" not in action:
        return "S4"
    elif "add" in action and "x" not in action:
        return "S3"

    # Skill 2 - add a negative variable term to both sides
    # Skill 1 - add a positive variable term to both sides
    if "add" in action and "-" in action and "x" in action:
        return "S2"
    elif "add" in action and "x" in action:
        return "S1"

    return "We have a big problem :("

def test_step_through_problem():
    run_data = [
        {
            "equation": '3x+2=8',
            "action": "add -2"
        },
        {
            "equation": '3x=8',
            "action": "divide 3"
        },
        {
            "equation": 'x=1+9',
            "action": "combine RHS constant terms" # Generates the CorrectStreak...
        },
        {
            "equation": 'x-2=4',
            "action": "divide 2"
        },
        {
            "equation": '2x+3x=9',
            "action": "combine RHS variable terms"
        },
        {
            "equation": '3x=2x+1',
            "action": "add -3x" # Generates the IncorrectStreak...
        }
    ]

    # The skills updated in the test run:
    current_skills = ['S8','S9']
    print("Skills: " + str(current_skills))
    for run in run_data:
        feedback, current_skills = stepThroughProblem(run["equation"], run["action"], current_skills, debug=True)
        print("\tUpdated skills: " + str(current_skills))
        print("\tFeedback msg: " + feedback)

# test_step_through_problem()
