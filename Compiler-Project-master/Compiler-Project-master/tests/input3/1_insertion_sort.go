package main

// InsertionSort sorts an array of integers.
func InsertionSort() {

	var ar [9]int
	var i int
	for i = 0; i < 9; i++ {
		ar[i] = i
	}

	for i = 0; i < 9; i++ {
		var max, ind int
		max = ar[i]
		ind = i
		var j int
		for j = i + 1; j < 9; j++ {
			if ar[j] > max {
				max = ar[j]
				ind = j
			}
		}
		var t int
		t = ar[i]
		ar[i] = ar[ind]
		ar[ind] = t
	}

	for i=0; i<9;i++{
		printInt ar[i]
	}
}

func main() {
	InsertionSort()
}
