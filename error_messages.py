UNSUPPORTED_ARITHMETIC_OPERATION = "Unsupported arithmetic operation. Unable to perform the operation on a non-numeric data type."
CYCLIC_DEPENDENCY = "Cyclic dependency detected"
RECURSIVE_DEPENDENCY_BETWEEN_RECORDS = "Recursive dependencies between records"


def alias_defined(alias_name):
    return f"Alias already defined: {alias_name}"


def record_defined(record_name):
    return f"Record already defined: {record_name}"


def undefined_record(record_name):
    return f"Undefined record: {record_name}"


def undefined_element(element):
    return f"{element} is not defined"


def undefined_alias(alias):
    return f"Undefined alias: {alias}"


def no_attribute(obj, attribute):
    return f"{obj} object has no attribute {attribute}"