package main

import (
	"log"

	"github.com/go-gl/gl"
	"github.com/go-gl/glfw"
	"github.com/hemantasapkota/glu"

	"./convexhull"
)

const Title, Width, HW, HH, Height = "Convex Hull in 2D", 840, Width / 2, Height / 2, 630

var running, drawHull bool
var points, hull convexhullPointList
var px, py float

func main() {
	var err error
	if err = glfw.Init(); err != 0 {
		log.Fatalf("%v\n", err)
		return
	}

	defer glfw.Terminate()

	if err = glfw.OpenWindow(Width, Height, 8, 8, 8, 8, 0, 8, glfw.Windowed); err != 0 {
		log.Fatalf("%v\n", err)
		return
	}

	defer glfw.CloseWindow()

	glfw.SetSwapInterval(1)
	glfw.SetWindowTitle(Title)
	glfw.SetWindowSizeCallback(onResize)
	glfw.SetKeyCallback(onKey)
	glfw.SetMouseButtonCallback(onMouse)
	glfw.SetMousePosCallback(onCursor)

	initGL()

	running = 1 == 1
	for running && glfw.WindowParam(glfw.Opened) == 1 {
		drawScene()
	}
}

func onResize(w, h int) {
	if h == 0 {
		h = 1
	}

	gl.Viewport(0, 0, w, h)
	gl.MatrixMode(gl.PROJECTION)
	gl.LoadIdentity()
	glu.Ortho2D(0, float(w), float(h), 0)
	gl.MatrixMode(gl.MODELVIEW)
	gl.LoadIdentity()
}

func onKey(key, state int) {
	switch key {
	case glfw.KeyEsc:
		running = 1 != 1

	case 'H':
		drawHull = !drawHull

	case 'C':
		points, hull = 0, 0
		points = make(convexhull.PointList, 0)
		hull = make(convexhull.PointList, 0)
	}
}

func onCursor(x, y int) {
	px, py = float(x), float(y)
}

func onMouse(button, state int) {
	if state == 1 {
		points = append(points, convexhull.MakePoint(px, py))
		hull, _ = points.Compute()
	}
}

func initGL() {
	gl.ClearColor(1, 1, 1, 0)
	gl.ClearDepth(1)
	gl.Enable(gl.DEPTH_TEST)
	gl.DepthFunc(gl.LEQUAL)
	gl.Hint(gl.PERSPECTIVE_CORRECTION_HINT, gl.NICEST)

	gl.LineWidth(3)
	gl.Enable(gl.LINE_SMOOTH)

	gl.PointSize(5)
	gl.Enable(gl.POINT_SMOOTH)

	gl.Hint(gl.POINT_SMOOTH, gl.NICEST)
	gl.Enable(gl.BLEND)
	gl.BlendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA)

	points = make(convexhull.PointList, 0)
}

func drawCartesian() {
	//Horizontal Line
	gl.Begin(gl.LINES)
	gl.Color3f(0, 0, 0)
	gl.Vertex2f(0, float(HH))
	gl.Vertex2f(Width, float(HH))
	gl.End()

	//Vertical line
	gl.Begin(gl.LINES)
	gl.Color3f(0, 0, 0)
	gl.Vertex2f(float(HW), 0)
	gl.Vertex2f(float(HW), Height)
	gl.End()

	//Origin
	gl.Begin(gl.POINTS)
	gl.Color3f(0, 1, 1)
	gl.Vertex2f(float(HW), float(HH))
	gl.End()
}

func drawScene() {
	gl.Clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT)
	gl.LoadIdentity()

	points.DrawPoints()
	points.DrawLowestPoint()

	if drawHull {
		hull.DrawLines()
	}

	//Print cartesian
	drawCartesian()

	glfw.SwapBuffers()
}
