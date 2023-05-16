package main;
import "fmt";

// type f struct{
// 	a int
// 	b *f
// }
func binarySearch(sortedList [20]int, lookingFor int, lo int, hi int) int {
  
  if hi<lo{
  	return -1
  }
  var mid int = lo + (hi-lo)/2
  
  var midValue int = sortedList[mid]
 

  if midValue == lookingFor {
    return mid
  } else if midValue > lookingFor {
    // We want to use the left half of our list
    hi = mid - 1
  } else {
    // We want to use the right half of our list
    lo = mid + 1
  }
  // return 1
  return binarySearch(sortedList,lookingFor,lo,hi)

}


func ar_print(ar [5]int){
	for k:=0;k<5;k++{
		printInt ar[k]
	}
}


func main()int{
	// f();
	// var r f
	// r.a=1
	// var c int=5
	// var e float32=12.0
	var ar [20] int
	for k:=0;k<20;k++{
		ar[k]=2*k
	}
	var t int = binarySearch(ar,2,0,20)
	printInt t	

}

