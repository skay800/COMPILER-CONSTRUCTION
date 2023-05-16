package main

type hello struct {
	a int
	b float32
}

func main() {
	var h hello
	h.a = 1
	h.b = 1
	h.c = h.a + h.b
}
