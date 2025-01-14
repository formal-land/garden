"""
Translate Circom circuits to Coq code.
"""
import json
import sys
from typing import Any, Tuple

def indent(text: str) -> str:
    return "\n".join("  " + line for line in text.split("\n"))

def escape_coq_name(name: str) -> str:
    reserved_names = [
        "as", "at", "cofix", "else", "end", "exists", "fix", "forall", "fun",
        "if", "in", "let", "match", "mod", "Prop", "return", "Set", "then",
        "Type", "using", "where", "with"
    ]
    if name in reserved_names:
        return name + "_"
    return name

def list_with_special_empty(items: list[str]) -> str:
    if len(items) == 0:
        return "([] : list F.t)"
    return "[ " + "; ".join(items) + " ]"

"""
pub type TagList = Vec<String>;
"""
def to_coq_tag_list(node) -> str:
    return "[" + ", ".join(f"\"{tag}\"" for tag in node) + "]"

"""
pub enum SignalType {
    Output,
    Input,
    Intermediate,
}
"""
def signal_type_to_coq(node) -> str:
    if "Output" in node:
        return "Output"
    if "Input" in node:
        return "Input"
    if "Intermediate" in node:
        return "Intermediate"
    return f"Unknown signal type: {node}"

"""
pub enum VariableType {
    Var,
    Signal(SignalType, TagList),
    Component,
    AnonymousComponent,
    Bus(String, SignalType, TagList),
}
"""
def to_coq_variable_type(node) -> str:
    if "Var" in node:
        return "Var"
    if "Signal" in node:
        signal = node["Signal"]
        return \
            "Signal " + signal_type_to_coq(signal[0])
    if "Component" in node:
        return "Component"
    if "AnonymousComponent" in node:
        return "AnonymousComponent"
    if "Bus" in node:
        bus = node["Bus"]
        return "Bus " + bus["String"] + " " + bus["SignalType"] + " " + bus["TagList"]
    return f"Unknown variable type: {node}"

"""
pub enum LogArgument {
    LogStr(String),
    LogExp(Expression),
}
"""
def to_coq_log_argument(node) -> str:
    if "LogStr" in node:
        return f"LogStr {node['LogStr']}"
    if "LogExp" in node:
        return f"LogExp {to_coq_expression(node['LogExp'])}"
    return f"Unknown log argument: {node}"

"""
pub enum Access {
    ComponentAccess(String),
    ArrayAccess(Expression),
}
"""
def to_coq_access(node) -> str:
    if "ComponentAccess" in node:
        return f"Access.Component \"{node['ComponentAccess']}\""
    if "ArrayAccess" in node:
        return f"Access.Array ({to_coq_expression(node['ArrayAccess'])})"
    return f"Unknown access: {node}"

def lower_case_first_letter(s: str) -> str:
    return s[0].lower() + s[1:]

def to_coq_big_int(node) -> str:
    digits = node[1]
    result = 0
    for index, digit in enumerate(digits):
        result += digit * 2 ** (32 * index)
    return str(result)

"""
pub enum Expression {
    InfixOp {
        meta: Meta,
        lhe: Box<Expression>,
        infix_op: ExpressionInfixOpcode,
        rhe: Box<Expression>,
    },
    PrefixOp {
        meta: Meta,
        prefix_op: ExpressionPrefixOpcode,
        rhe: Box<Expression>,
    },
    InlineSwitchOp {
        meta: Meta,
        cond: Box<Expression>,
        if_true: Box<Expression>,
        if_false: Box<Expression>,
    },
    ParallelOp {
        meta: Meta,
        rhe: Box<Expression>,
    },
    Variable {
        meta: Meta,
        name: String,
        access: Vec<Access>,
    },
    Number(Meta, BigInt),
    Call {
        meta: Meta,
        id: String,
        args: Vec<Expression>,
    },
    BusCall {
        meta: Meta,
        id: String,
        args: Vec<Expression>,
    },
    AnonymousComp{
        meta: Meta,
        id: String,
        is_parallel: bool,
        params: Vec<Expression>,
        signals: Vec<Expression>,
        names: Option<Vec<(AssignOp, String)>>,
    },
    ArrayInLine {
        meta: Meta,
        values: Vec<Expression>,
    },
    Tuple {
        meta: Meta,
        values: Vec<Expression>,
    },
    UniformArray {
        meta: Meta,
        value: Box<Expression>,
        dimension: Box<Expression>,
    },
}
"""
def to_coq_expression(node) -> str:
    if "InfixOp" in node:
        infix_op = node["InfixOp"]
        return \
            "InfixOp." + lower_case_first_letter(infix_op["infix_op"]) + " ~(| " + \
            to_coq_expression(infix_op["lhe"]) + ", " + \
            to_coq_expression(infix_op["rhe"]) + \
            " |)"
    if "PrefixOp" in node:
        prefix_op = node["PrefixOp"]
        return \
            "PrefixOp." + lower_case_first_letter(prefix_op["prefix_op"]) + " ~(| " + \
            to_coq_expression(prefix_op["rhe"]) + \
            " |)"
    if "InlineSwitchOp" in node:
        inline_switch_op = node["InlineSwitchOp"]
        return \
            "ternary_expression (" + \
            to_coq_expression(inline_switch_op["cond"]) + ") (" + \
            to_coq_expression(inline_switch_op["if_true"]) + ") (" + \
            to_coq_expression(inline_switch_op["if_false"]) + ")"
    if "ParallelOp" in node:
        parallel_op = node["ParallelOp"]
        return "ParallelOp " + to_coq_expression(parallel_op["rhe"])
    if "Variable" in node:
        variable = node["Variable"]
        if len(variable["access"]) == 0:
            return \
                "M.var ~(| " + \
                "\"" + variable["name"] + "\"" + \
                " |)"
        return \
            "M.var_access ~(| " + \
            "\"" + variable["name"] + "\"" + ", " + \
            "[" + "; ".join(to_coq_access(access) for access in variable["access"]) + "]" + \
            " |)"
    if "Number" in node:
        number = node["Number"]
        return to_coq_big_int(number[1])
    if "Call" in node:
        call = node["Call"]
        return \
            "M.call_function ~(| " + \
            "\"" + call["id"] + "\"" + ", " + \
            list_with_special_empty([
                to_coq_expression(arg)
                for arg in call["args"]
            ]) + \
            " |)"
    if "BusCall" in node:
        bus_call = node["BusCall"]
        return bus_call["id"] + "(" + ", ".join(to_coq_expression(arg) for arg in bus_call["args"]) + ")"
    if "AnonymousComp" in node:
        anonymous_comp = node["AnonymousComp"]
        return \
            "AnonymousComp " + anonymous_comp["id"] + " " + str(anonymous_comp["is_parallel"]) + " " + \
            ", ".join(to_coq_expression(param) for param in anonymous_comp["params"]) + " " + \
            ", ".join(to_coq_expression(signal) for signal in anonymous_comp["signals"])
    if "ArrayInLine" in node:
        array_in_line = node["ArrayInLine"]
        return list_with_special_empty([
            to_coq_expression(value)
            for value in array_in_line["values"]
        ])
    if "Tuple" in node:
        tuple = node["Tuple"]
        return \
            "Tuple {" + ", ".join(to_coq_expression(value) for value in tuple["values"]) + "}"
    if "UniformArray" in node:
        uniform_array = node["UniformArray"]
        return \
            "array_with_repeat (" + to_coq_expression(uniform_array["value"]) + ") (" + \
            to_coq_expression(uniform_array["dimension"]) + ")"
    return f"Unknown expression: {node}"

def flatten_blocks(node) -> list:
    if node is None:
        return []
    if "Block" in node:
        block = node["Block"]
        return [
            flat_stmt
            for stmt in block["stmts"]
            for flat_stmt in flatten_blocks(stmt)
        ]
    return [node]

"""
pub enum Statement {
    IfThenElse {
        meta: Meta,
        cond: Expression,
        if_case: Box<Statement>,
        else_case: Option<Box<Statement>>,
    },
    While {
        meta: Meta,
        cond: Expression,
        stmt: Box<Statement>,
    },
    Return {
        meta: Meta,
        value: Expression,
    },
    InitializationBlock {
        meta: Meta,
        xtype: VariableType,
        initializations: Vec<Statement>,
    },
    Declaration {
        meta: Meta,
        xtype: VariableType,
        name: String,
        dimensions: Vec<Expression>,
        is_constant: bool,
    },
    Substitution {
        meta: Meta,
        var: String,
        access: Vec<Access>,
        op: AssignOp,
        rhe: Expression,
    },
    MultSubstitution {
        meta: Meta,
        lhe: Expression,
        op: AssignOp,
        rhe: Expression,
    },
    UnderscoreSubstitution{
        meta: Meta,
        op: AssignOp,
        rhe: Expression,
    },
    ConstraintEquality {
        meta: Meta,
        lhe: Expression,
        rhe: Expression,
    },
    LogCall {
        meta: Meta,
        args: Vec<LogArgument>,
    },
    Block {
        meta: Meta,
        stmts: Vec<Statement>,
    },
    Assert {
        meta: Meta,
        arg: Expression,
    },
}
"""
def to_coq_statement(node) -> str:
    if "IfThenElse" in node:
        if_then_else = node["IfThenElse"]
        return \
            "do~ M.if_ [[ " + to_coq_expression(if_then_else["cond"]) + " ]] (* then *) (\n" + \
            indent(to_coq_statements(flatten_blocks(if_then_else["if_case"]))) + "\n" + \
            ") (* else *) (\n" + \
            indent(to_coq_statements(flatten_blocks(if_then_else["else_case"]))) + "\n" + \
            ") in"
    if "While" in node:
        while_stmt = node["While"]
        return \
            "do~ M.while [[ " + to_coq_expression(while_stmt["cond"]) + " ]] (\n" + \
            indent(to_coq_statement(while_stmt["stmt"])) + "\n" + \
            ") in"
    if "Return" in node:
        return "do~ M.return_ [[ " + to_coq_expression(node["Return"]["value"]) + " ]] in"
    if "InitializationBlock" in node:
        init_block = node["InitializationBlock"]
        return \
            "(* " + to_coq_variable_type(init_block["xtype"]) + " *)\n" + \
            "\n".join(to_coq_statement(stmt) for stmt in init_block["initializations"])
    if "Declaration" in node:
        declaration = node["Declaration"]
        xtype = declaration["xtype"]
        if xtype == "Var":
            declare_function = "M.declare_var"
        elif xtype == "Component":
            return "do~ M.declare_component \"" + declaration["name"] + "\" in"
        elif xtype == "AnonymousComponent":
            declare_function = "M.declare_anonymous_component"
        elif "Signal" in xtype:
            declare_function = "M.declare_signal"
        elif xtype == "Bus":
            declare_function = "M.declare_bus"
        else:
            declare_function = f"Unknown xtype {xtype}"
        return \
            "do~ " + declare_function + " \"" + declaration["name"] + "\" [[ " + \
            list_with_special_empty([
                to_coq_expression(dim) for dim in declaration["dimensions"]
            ]) + \
            " ]] in"
    if "Substitution" in node:
        substitution = node["Substitution"]
        return \
            "do~ M.substitute_var \"" + substitution["var"] + "\" " + \
            "[[ " + to_coq_expression(substitution["rhe"]) + " ]] in"
    if "MultSubstitution" in node:
        mult_substitution = node["MultSubstitution"]
        return \
            "MultSubstitution " + to_coq_expression(mult_substitution["lhe"]) + " = " + \
            to_coq_expression(mult_substitution["rhe"])
    if "UnderscoreSubstitution" in node:
        underscore_substitution = node["UnderscoreSubstitution"]
        return \
            "UnderscoreSubstitution = " + to_coq_expression(underscore_substitution["rhe"])
    if "ConstraintEquality" in node:
        constraint_equality = node["ConstraintEquality"]
        return \
            "do~ M.equality_constraint\n" + \
            indent(
                "[[ " + to_coq_expression(constraint_equality["lhe"]) + " ]]\n" + \
                "[[ " + to_coq_expression(constraint_equality["rhe"]) + " ]]"
            ) + "\n" + \
            "in"
    if "LogCall" in node:
        log_call = node["LogCall"]
        return \
            "LogCall " + ", ".join(to_coq_log_argument(arg) for arg in log_call["args"])
    if "Block" in node:
        stmts = flatten_blocks(node)
        return to_coq_statements(stmts)
    if "Assert" in node:
        return "do~ M.assert [[ " + to_coq_expression(node["Assert"]["arg"]) + " ]] in"
    return f"Unknown statement: {node}"

def to_coq_statements(stmts: list) -> str:
    return \
        "\n".join([
            *(to_coq_statement(stmt) for stmt in stmts),
            "M.pure BlockUnit.Tt",
        ])

def get_signals_in_template(template) -> list[Tuple[str, int]]:
    if "Block" in template["body"]:
        stmts = flatten_blocks(template["body"])
        return [
            (
                init_stmt["Declaration"]["name"],
                len(init_stmt["Declaration"]["dimensions"]),
            )
            for stmt in stmts
            if "InitializationBlock" in stmt
            for init_stmt in stmt["InitializationBlock"]["initializations"]
            if
               "Declaration" in init_stmt and
                "Signal" in init_stmt["Declaration"]["xtype"]
        ]

    return []

def get_signal_type(nb_dimensions: int) -> str:
    if nb_dimensions == 0:
        return "F.t"
    if nb_dimensions == 1:
        return "list F.t"
    return "list (" + get_signal_type(nb_dimensions - 1) + ")"

def to_coq_definition_args(args: list[str]) -> str:
    if len(args) == 0:
        return ""
    return " (" + " ".join(args) + " : F.t)"

"""
pub enum Definition {
    Template {
        meta: Meta,
        name: String,
        args: Vec<String>,
        arg_location: FileLocation,
        body: Statement,
        parallel: bool,
        is_custom_gate: bool,
    },
    Function {
        meta: Meta,
        name: String,
        args: Vec<String>,
        arg_location: FileLocation,
        body: Statement,
    },
    Bus {
        meta: Meta,
        name: String,
        args: Vec<String>,
        arg_location: FileLocation,
        body: Statement,
    },
}
"""
def to_coq_definition(node) -> str:
    if "Template" in node:
        template = node["Template"]
        signals = get_signals_in_template(template)
        return \
            "(* Template signals *)\n" + \
            "Module " + template["name"] + "Signals.\n" + \
            indent(
                "Record t : Set := {\n" +
                indent(
                    "\n".join(
                        escape_coq_name(signal[0]) + " : " +
                        get_signal_type(signal[1]) + ";"
                        for signal in signals
                    )
                ) + "\n" +
                "}."
            ) + "\n" + \
            "End " + template["name"] + "Signals.\n" + \
            "\n" + \
            "(* Template body *)\n" + \
            "Definition " + template["name"] + to_coq_definition_args(template["args"]) + \
            " : M.t (BlockUnit.t Empty_set) :=\n" + \
            indent(
                to_coq_statement(template["body"]) + "."
            )
    if "Function" in node:
        function = node["Function"]
        return \
            "(* Function *)\n" + \
            "Definition " + function["name"] + to_coq_definition_args(function["args"]) + \
            " : M.t F.t :=\n" + \
            indent(
                "M.function_body (\n" + \
                indent(
                    to_coq_statement(function["body"])
                ) + "\n" +
                ")."
            )
    if "Bus" in node:
        bus = node["Bus"]
        return \
            "(* Bus *)\n" + \
            "Definition " + bus["name"] + to_coq_definition_args(bus["args"]) + \
            " : Bus.t F.t :=\n" + \
            indent(
                to_coq_statement(bus["body"]) + "."
            )
    return f"Unknown definition: {node}"

"""
pub struct AST {
    pub meta: Meta,
    pub compiler_version: Option<Version>,
    pub custom_gates: bool,
    pub custom_gates_declared: bool,
    pub includes: Vec<String>,
    pub definitions: Vec<Definition>,
    pub main_component: Option<MainComponent>,
}
"""
def to_coq_ast(node) -> str:
    header = """
(* Generated by Garden *)
Require Import Garden.Garden.

"""
    return \
        header + \
        "\n\n".join(to_coq_definition(definition) for definition in node["definitions"])

# Load the first command line parameter
with open(sys.argv[1], "r") as f:
    json_data = f.read()

# Print the Coq code
print(to_coq_ast(json.loads(json_data)))
