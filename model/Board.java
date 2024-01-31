package ProgrammingProject.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Represents the game board for a grid-based line drawing game.
 * The board consists of a grid of dots with lines that can be drawn between them to form boxes.
 * It manages the state of the board, including the lines drawn and the scores of two players.
 */

public class Board {

    private final int DIM;

    private final Line[] allLines;

    private int blueScore = 0;
    private int redScore = 0;
    private Line currentPlayer = Line.BLUE;

    //@ public invariant DIM > 0;
    //@ public invariant allLines != null;
    //@ public invariant blueScore >= 0 && redScore >= 0;
    //@ public invariant currentPlayer == Line.BLUE || currentPlayer == Line.RED;

    /**
     * Constructs a Board with a specified dimension and initializes all lines on the board to be empty.
     *
     * @param DIM The dimension of the board, defining the number of dots in a row or column.
     */
    //@ requires DIM > 0;
    //@ ensures this.DIM == DIM;
    //@ ensures (\forall int i; i >= 0 && i < allLines.length; allLines[i] == Line.EMPTY);
    public Board(int DIM){
        this.DIM = DIM;
        allLines = new Line[((this.DIM - 1) * this.DIM) * 2];
        Arrays.fill(allLines, Line.EMPTY);
    }
    /**
     * Gets the dimension of the board.
     *
     * @return The dimension of the board.
     */
    //@ ensures \result == DIM;
    public int getDIM(){return DIM;}

    /**
     * Retrieves the status of a line by the indices of its start and end dots.
     *
     * @param start The index of the start dot.
     * @param end The index of the end dot.
     * @return The status of the line (EMPTY, BLUE, RED).
     */
    //@ requires isValidDot(start) && isValidDot(end);
    //@ ensures \result == allLines[getIndex(start, end)];
    public Line getLine(int start, int end){return allLines[getIndex(start, end)];}
    /**
     * Checks if a given dot index is valid on the board.
     *
     * @param dot The index of the dot.
     * @return True if the dot index is valid, false otherwise.
     */
    //@ ensures \result == (dot >= 0 && dot < DIM * DIM);
    public boolean isValidDot(int dot){return dot >= 0 && dot < (DIM*DIM);}
    /**
     * Checks if all lines on the board are filled.
     *
     * @return True if all lines are filled, indicating that no more moves can be made, false otherwise.
     */
    //@ ensures \result == (\forall int i; i >= 0 && i < allLines.length; allLines[i] != Line.EMPTY);
    public boolean isFull(){
        for (Line line : allLines){
            if (line == Line.EMPTY){
                return false;
            }
        }
        return true;
    }
    /**
     * Checks if the game is over, which occurs when the board is full.
     *
     * @return True if the game is over, false otherwise.
     */
    //@ ensures \result == isFull();
    public boolean gameOver(){
        return isFull();
    }
    /**
     * Determines if a player is currently leading in terms of score.
     *
     * @param line The line color representing the player (BLUE or RED).
     * @return True if the player is leading in score, false otherwise.
     */

    public boolean isLeading(Line line) {
        if (line == Line.BLUE) {
            return blueScore > redScore;
        } else {
            return redScore > blueScore;
        }
    }
    /**
     * Gets the score of a specific player.
     *
     * @param line The line color representing the player (BLUE or RED).
     * @return The score of the specified player.
     */

    public int getScore(Line line) {
        if (line == Line.RED) {
            return redScore;
        } else if (line == Line.BLUE) {
            return blueScore;
        } else {
            return -1;
        }
    }
    /**
     * Determines if the specified player is the winner.
     *
     * @param line The line color representing the player (BLUE or RED).
     * @return True if the player is the winner based on the current scores, false otherwise.
     */

    public boolean isWinner(Line line){
        return isLeading(line);
    }
    /**
     * Checks if there is a winner of the game, which occurs when the game is over and one player has a higher score.
     *
     * @return True if there is a winner, false if the game is a draw or not yet finished.
     */
    public boolean hasWinner(){
        return isWinner(Line.RED) || isWinner(Line.BLUE);
    }
    /**
     * Resets the board to its initial state with all lines empty.
     */
    public void reset(){
        Arrays.fill(allLines, Line.EMPTY);
    }
    /**
     * Performs a move on the board by drawing a line between two points.
     * The move is made by the current player and can only be made if the line is not already drawn
     * and the move is valid (i.e., the line is either horizontal or vertical and doesn't wrap around the board).
     *
     * @param start The starting point of the line.
     * @param end The ending point of the line.
     * @param line The color of the line representing the current player (BLUE or RED).
     */
    /*@
  requires isValidDot(start) && isValidDot(end);
  requires getLine(start, end) == Line.EMPTY; // Line must be empty to be drawn
  requires line == Line.BLUE || line == Line.RED; // Line color must be valid
  ensures
    // If a square is completed, the score of the current player increases
    (\old(checkSquare(start, end)) && line == Line.BLUE ==> blueScore == \old(blueScore + 1)) &&
    (\old(checkSquare(start, end)) && line == Line.RED ==> redScore == \old(redScore + 1)) &&
    // If no square is completed, it's the other player's turn
    (!\old(checkSquare(start, end)) ==> currentPlayer != \old(currentPlayer));
*/
    public void doMove(int start, int end, Line line){
        if (Math.abs(start - end) == 1 || Math.abs(start - end) == DIM){
            for (int edge = DIM - 1; edge < (DIM*DIM); edge += DIM){
                if ((start == edge && end == edge + 1) || (end == edge && start == edge + 1)){
                    return;
                }
            }

            int lineIndex = getIndex(start, end);
            if (lineIndex != -1){
                if (allLines[lineIndex] == Line.EMPTY){
                    allLines[lineIndex] = line;
                } else {
                    System.out.println("Line already exists");
                    return;
                }
            } else {
                return;
            }

            boolean scored = checkSquare(start , end);
            if (scored){
                if (line == Line.BLUE){
                    blueScore++;
                } else if (line == Line.RED) {
                    redScore++;
                }
            } else {
                currentPlayer = (currentPlayer == Line.BLUE) ? Line.RED : Line.BLUE;
            }
        }
    }
    /**
     * Checks if a line exists between two specified points.
     *
     * @param start The starting point of the line.
     * @param end The ending point of the line.
     * @return True if a line exists between the given points, false otherwise.
     */

    public boolean lineExists(int start, int end){
        if (getIndex(start, end) != -1){
            return allLines[getIndex(start, end)] != Line.EMPTY;
        }
        return false;
    }
    /**
     * Checks whether drawing a line completes a square.
     * This method is used to determine if the current player should get a point
     * for completing a square with their move.
     *
     * @param start The starting point of the line.
     * @param end The ending point of the line.
     * @return True if drawing the line completes a square, false otherwise.
     */
    /*@
  requires isValidDot(start) && isValidDot(end);
  ensures \result == true <==>
    // Specific conditions when a square is completed, which depends on the game's rules
    // This is a simplified placeholder, actual conditions depend on the game logic
    (\exists int i; i >= 0 && i < allLines.length; allLines[i] == Line.EMPTY);
*/
    public boolean checkSquare(int start, int end){
        if (Math.abs(start - end) == 1){
            boolean horizontalTop = false;
            boolean horizontalBottom = false;

            for (int i = 0; i < DIM; i++){
                if (start == i){
                    horizontalTop = true;
                }
            }
            if (horizontalTop) {
                boolean lineAboveExists = lineExists(start + DIM, end + DIM);
                boolean verticalLineAtStartExists = lineExists(start + DIM, start);
                boolean verticalLineAtEndExists = lineExists(end + DIM, end);

                return lineAboveExists && verticalLineAtStartExists && verticalLineAtEndExists;
            }

            horizontalBottom = start >= (DIM * DIM - DIM) && start < DIM * DIM;

            if (horizontalBottom) {
                boolean lineBelowExists = lineExists(start - DIM, end - DIM);
                boolean verticalLineAtStartExists = lineExists(start - DIM, start);
                boolean verticalLineAtEndExists = lineExists(end - DIM, end);

                return lineBelowExists && verticalLineAtStartExists && verticalLineAtEndExists;
            }

            return lineExists(start - DIM, end - DIM) && lineExists(start - DIM, start) && lineExists(end - DIM, end)
                    || lineExists(start + DIM, end + DIM) && lineExists(start + DIM, start) && lineExists(end + DIM, end);


        }
        else if (Math.abs(start - end) == DIM) {
            boolean rightVEdge = start % DIM == (DIM - 1);
            boolean leftVEdge = start % DIM == 0;

            if (rightVEdge) {
                return lineExists(start - 1, end - 1) && lineExists(start - 1, start) && lineExists(end - 1, end);
            } else if (leftVEdge) {
                return lineExists(start + 1, end + 1) && lineExists(start + 1, start) && lineExists(end + 1, end);
            } else {
                return lineExists(start + 1, end + 1) && lineExists(start + 1, start) && lineExists(end + 1, end)
                        || lineExists(start - 1, end - 1) && lineExists(start - 1, start) && lineExists(end - 1, end);
            }
        }
        return false;
    }
    /**
     * Calculates the index of a line in the array of lines based on the start and end points.
     * This method determines whether the line is horizontal or vertical and computes its index.
     * It returns -1 if the start or end point is invalid or if no line exists between them.
     *
     * @param start The index of the start point.
     * @param end The index of the end point.
     * @return The index of the line in the array, or -1 if invalid.
     */
    /*@
  requires isValidDot(start) && isValidDot(end);
  ensures
    (\result >= 0 && \result < allLines.length) || \result == -1;
  ensures
    ((Math.abs(start - end) == 1 || Math.abs(start - end) == DIM) ==> \result != -1)
*/
    public int getIndex(int start, int end){
        if (!isValidDot(start) || !isValidDot(end)){
            return -1;
        }
        if (Math.abs(start - end) == 1){
            return Math.min(start,end) - (start / DIM);
        } else if (Math.abs(start - end) == DIM) {
            int totalHLines = (DIM - 1) * DIM;
            return totalHLines + Math.min(start, end);
        }
        return -1;
    }
    /**
     * Gets the start and end points of a line given its index in the array of lines.
     * This method is used to retrieve the corresponding points of a line, distinguishing
     * between horizontal and vertical lines.
     *
     * @param index The index of the line in the array.
     * @return A list containing the start and end points of the line.
     */

    public List<Integer> getPoints(int index) {
        int horizontalLines = (DIM - 1) * DIM;
        List<Integer> linePoints = new ArrayList<>();
        int start, end;

        if (index < horizontalLines) {
            // It's a horizontal line
            int row = index / (DIM - 1);
            int col = index % (DIM - 1);
            start = row * DIM + col;
            end = start + 1;
        } else {
            // It's a vertical line
            index -= horizontalLines;
            int col = index / (DIM - 1);
            int row = index % (DIM - 1);
            start = row * DIM + col;
            end = start + DIM;
        }

        linePoints.add(start);
        linePoints.add(end);
        return linePoints;
    }

    public Board deepCopy(){
        Board copy = new Board(this.DIM);
        System.arraycopy(this.allLines, 0, copy.allLines, 0, this.allLines.length);

        copy.blueScore = this.blueScore;
        copy.redScore = this.redScore;
        copy.currentPlayer = this.currentPlayer;

        return copy;
    }
    /**
     * Generates a string representation of the board's current state, suitable for text-based visualization.
     *
     * @return A string representing the board, including dots, lines, and scores.
     */
    //@ ensures \result != null;
    public String toString() {
        StringBuilder result = new StringBuilder();

        for (int row = 0; row < DIM; row++) {
            if (row > 0) {
                for (int col = 0; col < DIM; col++) {
                    int lineIndex = getIndex((row - 1) * DIM + col, row * DIM + col);
                    if (allLines[lineIndex] == Line.BLUE) {
                        String blueVLine = "\u001B[34m│\u001B[0m";
                        result.append(blueVLine);
                    } else if (allLines[lineIndex] == Line.RED) {
                        String redVLine = "\u001B[31m│\u001B[0m";
                        result.append(redVLine);
                    } else {
                        result.append(" ");
                    }
                    result.append("   ");
                }
                result.append("\n");
            }

            for (int col = 0; col < DIM; col++) {
                result.append("⦿");
                if (col < DIM - 1) {
                    int lineIndex = getIndex(row * DIM + col, row * DIM + col + 1);
                    if (allLines[lineIndex] == Line.BLUE) {
                        String blueHLine = "\u001B[34m———\u001B[0m";
                        result.append(blueHLine);
                    } else if (allLines[lineIndex] == Line.RED) {
                        String redHLine = "\u001B[31m———\u001B[0m";
                        result.append(redHLine);
                    } else {
                        result.append("   ");
                    }
                }
            }

            result.append("\n");
        }

        return result.toString();
    }

}
