try:
    from termcolor import colored
except ImportError:
    def colored(message, color, attrs):
        return message
    pass

from sys import stderr
from functools import wraps

def warn(message):
    print(colored(u"Warning: {0}".format(message), 'yellow', attrs=['bold']), file = stderr)

def notice(message):
    print(colored(u"Notice: {0}".format(message), 'white', attrs=['bold']), file = stderr)

def error(message, abort = False):
    print(colored(u"Error: {0}".format(message), 'red', attrs=['bold']), file = stderr)
    if abort:
        error("Fatal. Aborting")
        exit(1)

def trace(func):
    @wraps(func)
    def new_func(*args, **kwargs):
        res = func(*args, **kwargs)
        print("Call to function `{}' with positional arguments {}, keyword arguments {} and result `{}'".format(func.__name__, str(args), str(kwargs), str(res)))
        return res

    return new_func
