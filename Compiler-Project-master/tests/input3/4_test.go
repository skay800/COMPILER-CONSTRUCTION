package main

type person struct {
	name    string
	ager    [5]int
	address string
	home    string
}

func shift(c int) int {
	for k := 0; k <= 10; k++ {
		c++
	}
	return c
}

func main() {
	type p person
	p.ager[0] = 100
	p.ager[1] = shift(p.ager[0])
}
