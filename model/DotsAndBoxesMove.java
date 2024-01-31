package ProgrammingProject.model;

/**
 * Represents a move in the Dots and Boxes game, including the line color and positions between which the line is drawn.
 */

public class DotsAndBoxesMove implements Move {

    private final Line line;
    private int start;
    private int end;
    private int index;

    /**
     * Constructs a DotsAndBoxesMove with specified line color, start, and end points.
     *
     * @param line  The color of the line.
     * @param start The starting point of the line.
     * @param end   The ending point of the line.
     */
    /*@
      @ requires line != null;
      @ requires start >= 0 && end >= 0;
      @ ensures getLine() == line;
      @ ensures getStart() == start;
      @ ensures getEnd() == end;
      @*/

    public DotsAndBoxesMove(Line line, int start, int end){
        this.line = line;
        this.start = start;
        this.end = end;
    }

    /**
     * Returns the color of the line for this move.
     *
     * @return The line color.
     */
    /*@ pure @*/

    public Line getLine(){
        return line;
    }
    /**
     * Returns the starting point of the line.
     *
     * @return The starting point index.
     */
    /*@ pure @*/

    public int getStart(){
        return start;
    }
    /**
     * Sets the starting point of the line.
     *
     * @param start The starting point index to set.
     */
    /*@
      @ requires start >= 0;
      @ ensures getStart() == start;
      @*/

    public void setStart(int start){
        this.start = start;
    }
    /**
     * Returns the ending point of the line.
     *
     * @return The ending point index.
     */
    /*@ pure @*/

    public int getEnd(){
        return end;
    }
    /**
     * Sets the ending point of the line.
     *
     * @param end The ending point index to set.
     */
    /*@
      @ requires end >= 0;
      @ ensures getEnd() == end;
      @*/

    public void setEnd(int end){
        this.end = end;
    }

    /**
     * Gets the index of the line if it has been set, used for identifying specific moves.
     *
     * @return The line index.
     */
    /*@ pure @*/

    public int getIndex(){
        return index;
    }
    /**
     * Provides a string representation of the move, showing the start and end points.
     *
     * @return A string representation of the move.
     */
    /*@
      @ ensures \result != null;
      @*/

    public String toString(){
        return start+"-"+end;
    }

}
