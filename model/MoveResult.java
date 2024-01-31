package ProgrammingProject.model;

/**
 * Represents the result of evaluating a move in the game.
 * This class holds both the evaluation value of the move, which can be used for scoring or decision-making,
 * and the move itself.
 */
public class MoveResult {
    /**
     * The evaluation value of the move. Higher values typically indicate better moves.
     */
    public int value;

    /**
     * The move associated with this result.
     */
    public DotsAndBoxesMove move;
    /**
     * Constructs a MoveResult with a specified value and move.
     *
     * @param value The evaluation value of the move.
     * @param move  The move being evaluated.
     */
    /*@
      @ requires move != null;
      @ ensures this.value == value;
      @ ensures this.move == move;
      @*/
    public MoveResult(int value, DotsAndBoxesMove move){
        this.value = value;
        this.move = move;
    }
}
