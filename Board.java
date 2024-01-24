package ProgrammingProject;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Represents the playing board for a game, such as Dots and Boxes.
 * This class manages the state of the board, including filled fields and completed boxes.
 */

public class Board {

    public static final int DIM = 6;

    private List<Integer> filled;

    private Set<Integer> completedBoxes;

    /**
     * Constructs a new Board instance.
     * Initializes the lists for filled fields and completed boxes.
     */

    public Board() {
        filled = new ArrayList<>();
        completedBoxes = new HashSet<>();
    }

    /**
     * Creates a deep copy of this Board instance.
     * @return A new Board instance with the same state as the current board.
     */

    public Board deepCopy() {
        Board copy = new Board();
        copy.filled.addAll(this.filled);
        return copy;
    }

    /**
     * Checks if a field is within the board.
     * @param field The field to check.
     * @return true if the field is within the board's dimensions, false otherwise.
     */

    public boolean isField(int field) {
        return field >= 0 && field < (DIM * DIM);
    }

    /**
     * Marks a box as completed.
     * @param boxTopLeft The top-left field number of the box.
     */

    public void markBoxCompleted(int boxTopLeft){
        completedBoxes.add(boxTopLeft);
    }

    /**
     * Checks if a field is already filled.
     * @param field The field to check.
     * @return true if the field is filled, false otherwise.
     */

    public boolean isFilled(int field) {
        return filled.contains(field);
    }

    /**
     * Returns a string representation of the board.
     * @return A string showing the board's current state.
     */

    public String toString() {
        StringBuilder boardString = new StringBuilder();

        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                int field = row * DIM + col;

                // Add a space or dot based on whether the field is filled
                boardString.append(isFilled(field) ? "X" : ".");

                if (col < DIM - 1) {
                    if (isFilled(field) && isFilled(field + DIM) && isFilled(field + 1)) {
                        // Add a horizontal line if the adjacent fields are filled
                        boardString.append("-");
                    } else {
                        // Add a space for separation
                        boardString.append(" ");
                    }
                } else {
                    // Last column, add a newline
                    boardString.append("\n");
                }
            }

            if (row < DIM - 1) {
                for (int col = 0; col < DIM; col++) {
                    int field = row * DIM + col;

                    if (isField(field) && isField(field + 1) && isFilled(field + DIM)) {
                        // Add a vertical line if the adjacent fields are filled
                        boardString.append("| ");
                    } else {
                        // Add two spaces for separation
                        boardString.append("  ");
                    }
                }
                boardString.append("\n");
            }
        }

        return boardString.toString();
    }

    /**
     * Resets the board by clearing all filled fields.
     */
    public void reset() {
        filled.clear();
    }
    /**
     * Checks if a box is completed.
     * @param boxTopLeft The top-left field number of the box to check.
     * @return true if the box is completed, false otherwise.
     */
    public boolean isBoxCompleted(int boxTopLeft) {
        return completedBoxes.contains(boxTopLeft);
    }

    /**
     * Retrieves a list of valid moves based on the current board state.
     * @return A list of integers representing the fields that can be filled.
     */
    public List<Integer> getValidMoves() {
        List<Integer> validMoves = new ArrayList<>();

        for (int field = 0; field < DIM * DIM; field++) {
            if (!isFilled(field)) {
                validMoves.add(field);
            }
        }

        return validMoves;
    }

    /**
     * Fills a specified field on the board.
     * @param field The field to fill.
     */

    public void fill(int field) {
        if (isField(field) && !isFilled(field)) {
            filled.add(field);
        }
    }

    /**
     * Main method for demonstrating the Board class.
     * @param args Command-line arguments (not used).
     */

    public static void main(String[] args) {
        Board board = new Board();

        // Fill all the fields in the board
        for (int i = 0; i < DIM * DIM; i++) {
            board.fill(i);
        }
        System.out.println("Board state:\n" + board.toString());
    }
}
