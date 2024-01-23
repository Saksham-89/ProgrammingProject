package ProgrammingProject;

import java.util.*;

public class Board {

    public static final int DIM = 6;

    private boolean[][] horizontalLines;
    private boolean[][] verticalLines;

    private List<Integer> filled;

    private Set<Integer> completedBoxes;

    public Board() {
        filled = new ArrayList<>();
        completedBoxes = new HashSet<>();
        horizontalLines = new boolean[DIM * (DIM - 1)][DIM];
        verticalLines = new boolean[DIM * (DIM - 1)][DIM];
    }

    public boolean isLine(int line, boolean isHorizontal) {
        return line >= 0 && line < DIM * (DIM - 1) && (isHorizontal ? line % DIM == 0 : line % DIM != 0);
    }

    public boolean isLineDrawn(int line, boolean isHorizontal) {
        return isHorizontal ? horizontalLines[line][0] : verticalLines[line][0];
    }

    public void drawLine(int line, boolean isHorizontal) {
        if (isHorizontal) {
            horizontalLines[line][0] = true;
        } else {
            verticalLines[line][0] = true;
        }
    }

    public int[] getAdjacentLines(int line, boolean isHorizontal) {
        int dot1, dot2;
        if (isHorizontal) {
            dot1 = line / DIM * DIM + line % DIM;
            dot2 = dot1 + 1;
        } else {
            dot1 = line % DIM * DIM + line / DIM;
            dot2 = dot1 + DIM;
        }
        return new int[]{dot1, dot2};
    }

    public boolean isBoxCompleted(int row, int col) {
        int boxTopLeft = row * (DIM - 1) + col;
        return completedBoxes.contains(boxTopLeft);
    }

    public Board deepCopy() {
        Board copy = new Board();
        copy.filled.addAll(this.filled);
        return copy;
    }

    public boolean isField(int field) {
        return field >= 0 && field < (DIM * DIM);
    }

    public void markBoxCompleted(int boxTopLeft) {
        completedBoxes.add(boxTopLeft);
    }

    public boolean isFilled(int field) {
        return filled.contains(field);
    }

    public String toString() {
        StringBuilder boardString = new StringBuilder();

        for (int row = 0; row < DIM * 2 - 1; row++) {
            for (int col = 0; col < DIM * 2 - 1; col++) {
                if (row % 2 == 0 && col % 2 == 0) {
                    // Dot
                    boardString.append(".   ");
                } else if (row % 2 == 0 && col % 2 == 1 && col / 2 < DIM - 1) {
                    // Horizontal line
                    boardString.append(horizontalLines[row / 2][col / 2] ? "-   " : "    ");
                } else if (row % 2 == 1 && col % 2 == 0 && row / 2 < DIM - 1) {
                    // Vertical line
                    boardString.append(verticalLines[row / 2][col / 2] ? "|   " : "    ");
                } else {
                    // Space between dots
                    boardString.append("    ");
                }
            }

            boardString.append("\n");
        }

        return boardString.toString();
    }


    public void reset() {
        filled.clear();
        completedBoxes.clear();
        horizontalLines = new boolean[DIM][DIM - 1];
        verticalLines = new boolean[DIM - 1][DIM];
    }

    public boolean isBoxCompleted(int boxTopLeft) {
        return completedBoxes.contains(boxTopLeft);
    }

    public List<Integer> getValidMoves() {
        List<Integer> validMoves = new ArrayList<>();

        // Add dot moves
        for (int dot = 0; dot < DIM * DIM; dot++) {
            if (!isFilled(dot)) {
                validMoves.add(dot);
            }
        }

        // Add vertical line moves
        for (int row = 0; row < DIM - 1; row++) {
            for (int col = 0; col < DIM; col++) {
                int moveNumber = col + row * (DIM - 1) + DIM * DIM;
                validMoves.add(moveNumber);
            }
        }

        return validMoves;
    }



    public void fill(int field) {
        if (isField(field) && !isFilled(field)) {
            filled.add(field);
            checkForBoxes();
        }
    }

    private void checkForBoxes() {
        for (int row = 0; row < DIM - 1; row++) {
            for (int col = 0; col < DIM - 1; col++) {
                int boxTopLeft = row * (DIM - 1) + col;

                // Check if the box is completed
                if (verticalLines[row][col] && verticalLines[row + 1][col] &&
                        horizontalLines[row][col] && horizontalLines[row][col + 1]) {

                    // Update the completed boxes
                    completedBoxes.add(boxTopLeft);
                }
            }
        }
    }

    public static void main(String[] args) {
        Board board = new Board();
        System.out.println("Initial state: ");
        System.out.println(board.toString());
    }
}
