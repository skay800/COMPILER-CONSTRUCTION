package main

func main() {
	var a int = 20
	var ip *int
	ip = &a
	*ip = 1
	if a == 1 {
		*ip = 2
	}
}
