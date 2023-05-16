package main

const a, b, c, d = 5, 6, 7, 8

var x, y int = a + c, 6

var z int

func testing() {

}

func main() {
	var g int = 5
	g += 6

	if 1 < 5 {
		g += 5
	} else if 5 < 7 && g == 11 {
		g = 15
	} else if 1 == 1 {
		g = 4
	} else {
		g = 7
	}

	var i, j int
koko:
	for i = 0; i < 5; i++ {
		var j int
		g += 2
		for j = 0; j < 6; j++ {
		}
	}

	printf("%d %d %d\n", g, x, y)

	return testing()
}
