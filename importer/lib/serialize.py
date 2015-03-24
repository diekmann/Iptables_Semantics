from enum import Enum

from lib.util import error

class Constr_Syntax(Enum):
    imp = 1
    fun = 2

class Serializer:
    def __init__(self, module, import_module, constr_syntax):
        self.module = module
        self.import_module = import_module
        self.constr_syntax = constr_syntax

    def constr(self, f, *args):
        if self.constr_syntax == Constr_Syntax.imp:
            fmt = ","
            braces = "({})"
        else:
            fmt = " "
            braces = " {}"

        return f + braces.format(fmt.join(["({})".format(arg) for arg in args]))

    def quote(self, string):
        return string.replace('"', '\\"')

    def ipv4(self, *parts):
        assert len(parts) == 4
        parts = [self.nat(part) for part in parts]
        return self.tup(*parts)
        
    def nat(self, n):
        if type(n) is int:
            assert n >= 0
        elif type(n) is str:
            assert int(n) >= 0
        else:
            assert False
            
        return "{}".format(n)

class HOL(Serializer):
    def __init__(self, module, import_module):
        if import_module is None:
            default_import = "Code_Interface" #file Code_Interface.thy
            print("HOL: Import module name not specified. Using `%s'" % default_import)
            import_module = default_import

        super().__init__(module, import_module, Constr_Syntax.fun)

    def string(self, string):
        if "\"" in string:
            print("String `%s' should not contain quotes" % string)
        return "''{}''".format(string.replace('"', ''))

    def tup(self, *args):
        return "({})".format(",".join(args))

    def list(self, items):
        return "[{}]".format(",\n".join(items))

    def map(self, items):
        return "[{}]".format(",\n".join(["""{} \<mapsto> {}""".format(k, v) for k, v in items]))

    def definition(self, name, value):
        return 'definition "{} = {}"'.format(name, value)

    def header(self):
        return "theory {}\nimports matching {}\nbegin\n".format(self.module, self.import_module)

    def footer(self):
        return "\nend\n"

class ML(Serializer):
    def __init__(self, module, import_module):
        super().__init__(module, import_module, Constr_Syntax.imp)

    def string(self, string):
        return 'String.explode "{}"'.format(self.quote(string))

    def tup(self, *args):
        assert len(args) >= 2
        if len(args) == 2:
            tail = str(args[1])
        else:
            tail = self.tup(*args[1:])

        return "({}, {})".format(args[0], tail)

    def list(self, items):
        return "[{}]".format(",\n".join(items))

    def map(self, items):
        # Actually a list of tuples, but oh well
        return "[{}]".format(",\n".join(["({}, {})".format(k, v) for k, v in items]))

    def definition(self, name, value):
        return 'val {} = {};'.format(name, value)

    def header(self):
        import_str = "open {}".format(self.import_module) if self.import_module is not None else ""
        return "structure {} = struct\n{}\n".format(self.module, import_str)

    def nat(self, n):
        return "(nat_of_integer {})".format(n)

    def footer(self):
        return "\nend\n"

class Scala(Serializer):
    def __init__(self, import_module, module):
        error("unmaintained scala serializer")
        super().__init__(module, import_module, Constr_Syntax.imp)

    def string(self, string):
        return '"{}"'.format(string)

    def tup(self, *args):
        return "({})".format(",".join(args))

    def list(self, items):
        return "List({})".format(",\n".join(items))

    def map(self, items):
        return "Map({})".format(",\n".join(["{} -> {}".format(k, v) for k, v in items]))

    def definition(self, name, value):
        return 'val {} = {};'.format(name, value)

    def header(self):
        import_str = "import {}._".format(self.import_module) if self.import_module is not None else ""
        return "object {} {{\n{}\n".format(self.module, import_str)

    def footer(self):
        return "\n}\n"
