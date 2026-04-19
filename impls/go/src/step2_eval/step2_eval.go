package main

import (
	"errors"
	"fmt"
	"strings"
)

import (
	"mal/src/printer"
	"mal/src/reader"
	"mal/src/readline"
	. "mal/src/types"
)

// read
func READ(str string) (MalType, error) {
	return reader.Read_str(str)
}

// eval
func map_eval(xs []MalType, env map[string]MalType) ([]MalType, error) {
	lst := []MalType{}
	for _, a := range xs {
		exp, e := EVAL(a, env)
		if e != nil {
			return nil, e
		}
		lst = append(lst, exp)
	}
	return lst, nil
}

func EVAL(ast MalType, env map[string]MalType) (MalType, error) {

	// fmt.Printf("EVAL: %v\n", printer.Pr_str(ast, true))

	if Symbol_Q(ast) {
		env_val, env_found := env[ast.(Symbol).Val]
		if env_found {
 			return env_val, nil
		} else {
			return nil, errors.New("'" + ast.(Symbol).Val + "' not found")
		}
	} else if Vector_Q(ast) {
		lst, e := map_eval(ast.(Vector).Val, env)
		if e != nil {
			return nil, e
		}
		return Vector{lst, nil}, nil
	} else if HashMap_Q(ast) {
		m := ast.(HashMap)
		new_hm := HashMap{map[string]MalType{}, nil}
		for k, v := range m.Val {
			kv, e2 := EVAL(v, env)
			if e2 != nil {
				return nil, e2
			}
			new_hm.Val[k] = kv
		}
		return new_hm, nil
	} else if !List_Q(ast) {
		return ast, nil
	} else {
		// apply list
		if len(ast.(List).Val) == 0 {
			return ast, nil
		}

		a0 := ast.(List).Val[0]
			f, e := EVAL(a0, env)
			if e != nil {
				return nil, e
			}
			args := ast.(List).Val[1:]
			args, e = map_eval(args, env)
			if e != nil {
				return nil, e
			}
				fn, ok := f.(func([]MalType) (MalType, error))
				if !ok {
					return nil, errors.New("attempt to call non-function")
				}
				return fn(args)
		}
}

// print
func PRINT(exp MalType) (string, error) {
	return printer.Pr_str(exp, true), nil
}

var repl_env = map[string]MalType{
	"+": func(a []MalType) (MalType, error) {
		if e := assertArgNum(a, 2); e != nil {
			return nil, e
		}
		return a[0].(int) + a[1].(int), nil
	},
	"-": func(a []MalType) (MalType, error) {
		if e := assertArgNum(a, 2); e != nil {
			return nil, e
		}
		return a[0].(int) - a[1].(int), nil
	},
	"*": func(a []MalType) (MalType, error) {
		if e := assertArgNum(a, 2); e != nil {
			return nil, e
		}
		return a[0].(int) * a[1].(int), nil
	},
	"/": func(a []MalType) (MalType, error) {
		if e := assertArgNum(a, 2); e != nil {
			return nil, e
		}
		return a[0].(int) / a[1].(int), nil
	},
}

func assertArgNum(a []MalType, n int) error {
	if len(a) != n {
		return errors.New("wrong number of arguments")
	}
	return nil
}

// repl
func rep(str string) (MalType, error) {
	var exp MalType
	var res string
	var e error
	if exp, e = READ(str); e != nil {
		return nil, e
	}
	if exp, e = EVAL(exp, repl_env); e != nil {
		return nil, e
	}
	if res, e = PRINT(exp); e != nil {
		return nil, e
	}
	return res, nil
}

func main() {
	// repl loop
	for {
		text, err := readline.Readline("user> ")
		text = strings.TrimRight(text, "\n")
		if err != nil {
			return
		}
		var out MalType
		var e error
		if out, e = rep(text); e != nil {
			if e.Error() == "<empty line>" {
				continue
			}
			fmt.Printf("Error: %v\n", e)
			continue
		}
		fmt.Printf("%v\n", out)
	}
}
