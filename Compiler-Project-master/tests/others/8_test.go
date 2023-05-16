package main

import (
	"fmt"
	"sort"
)

func main() {

	strs := [3]string{"c", "a", "b"}
	sort.Strings(strs)
	fmt.Println("Strings:", strs)

	ints := [3]int{7, 2, 4}
	sort.Ints(ints)
	fmt.Println("Ints:   ", ints)

	s := sort.IntsAreSorted(ints)
	fmt.Println("Sorted: ", s)
}

type person struct {
	name           string
	age            [5]int
	address1, home string
}

var a, b, c = 1, 2, 3

func shit(c int) {
	e++
	f--
	for k = 1; k <= 10; k++ {
		e++
	}
	if i < 10 {
		g--
	}
}

func main(a int, b *string, c [5]***struct {
	c struct{ e int }
	d int
}) (a int, b ***struct {
	hello **int
	b     bool
}) {
}
