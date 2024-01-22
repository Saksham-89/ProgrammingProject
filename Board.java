package ProgrammingProject;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Board {

    public static final int DIM = 6;

    private List<Integer> filled;

    private Set<Integer> completedBoxes;

    public Board() {
        filled = new ArrayList<>();
        completedBoxes = new HashSet<>();
    }

    public Board deepCopy() {
        Board copy = new Board();
        copy.filled.addAll(this.filled);
        return copy;
    }

    public boolean isField(int field) {
        return field >= 0 && field < (DIM * DIM);
    }

    public void markBoxCompleted(int boxTopLeft){
        completedBoxes.add(boxTopLeft);
    }

    public boolean isFilled(int field) {
        return filled.contains(field);
    }

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


    public void reset() {
        filled.clear();
    }
    public boolean isBoxCompleted(int boxTopLeft) {
        return completedBoxes.contains(boxTopLeft);
    }

    public List<Integer> getValidMoves() {
        List<Integer> validMoves = new ArrayList<>();

        for (int field = 0; field < DIM * DIM; field++) {
            if (!isFilled(field)) {
                validMoves.add(field);
            }
        }

        return validMoves;
    }

    public void fill(int field) {
        if (isField(field) && !isFilled(field)) {
            filled.add(field);
        }
    }

    public static void main(String[] args) {
        Board board = new Board();

        // Fill all the fields in the board
        for (int i = 0; i < DIM * DIM; i++) {
            board.fill(i);
        }
        System.out.println("Board state:\n" + board.toString());
    }
}
