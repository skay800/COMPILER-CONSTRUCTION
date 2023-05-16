package main

func pluscommon(a int, b int) int {
	return a + b + b
}

func main() {
	var res int
	res = pluscommon(1, 2)
	var a float64
	a = 2.0 * res
}
