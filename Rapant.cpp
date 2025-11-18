#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#define U64 unsigned __int64
#define U32 unsigned __int32
#define U16 unsigned __int16
#define U8  unsigned __int8
#define S64 signed __int64
#define S32 signed __int32
#define S16 signed __int16
#define S8  signed __int8
#define MATE_VALUE 20000
#define TIME 300000
#define NAME "Rapant"
#define VERSION "2025-10-22"

using namespace std;

enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };

const int HASH_SIZE = 1 << 21;
const int INVALID = 32, EMPTY = 0, WHITE = 8, BLACK = 16;
const int B_QS = 4, B_KS = 8, W_QS = 1, W_KS = 2;
const int N_dirs[8] = { -21, -19, -12, -8, 8, 12, 19, 21 };
const int K_dirs[8] = { 1, 9, 10, 11, -1, -9, -10, -11 };
const int Q_dirs[8] = { 1, -1, 9, -9, -10, 10, -11, 11 };
const int R_dirs[4] = { 1, -1,  -10, 10 };
const int B_dirs[4] = { 9, -9, -11, 11 };
const int P_dirs[8] = { -10, -20, -9, -11, 10, 20, 9, 11 };
int inline static SRC(int Move) { return (Move & 0x7f); }
int inline static DST(int Move) { return ((Move >> 7) & 0x7f); }
int inline static PROMO(int Move) { return ((Move >> 14) & 3); }
int inline static VALUE(int Move) { return ((Move >> 16) & 0x3fff); }
int inline static SWITCH(int Color) { return Color ^ (WHITE | BLACK); }
int inline static File(int Sq) { return (Sq - 20) % 10; }
int inline static Rank(int Sq) { return (Sq - 10) / 10; }
int inline static SQ(int file, int rank) { return 21 + file + rank * 10; }
int inline static RelativeRank(int Sq, int col) { return col == BLACK ? (Sq - 10) / 10 : 9 - (Sq - 10) / 10; }
int EvalSq[26 * 128];
int SetCastle[120];
const int PieceValues[8] = { 100, 328, 330, 522, 952,0 };
const int KingEval[10] = { 0, 8, 12, 5, 0, 0, 5, 14, 9, 0 };
const int CentEval[10] = { 0,-6, -3, -1, 0, 0, -1, -3, -6, 0 };
const int Cent[10] = { 0, 1, 2, 2, 3, 3, 2, 1, 1, 0 };

const string SQSTR[65] = {
	"a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1",
	"a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2",
	"a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3",
	"a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4",
	"a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5",
	"a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6",
	"a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7",
	"a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8",
	"none"
};
string defFen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

static void PrintWelcome() {
	cout << NAME << " " << VERSION << endl;
}

static string MoveToUci(int move) {
	int src = SRC(move);
	int dst = DST(move);
	int sr = 8 - Rank(src);
	int sf = File(src) - 1;
	int dr = 8 - Rank(dst);
	int df = File(dst) - 1;
	int sqS = sr * 8 + sf;
	int sqD = dr * 8 + df;
	if (sqS < 0 || sqD < 0 || sqS>63 || sqD>63)return "error";
	return SQSTR[sqS] + SQSTR[sqD];
}

struct SBoard
{
	unsigned char board[120] = {};
	int color = WHITE, Eval = 0, EPsq = 0, Castling = 0, WKsq = 95, BKsq = 25, WMat = 0, BMat = 0, nMoves = 0, nLastCapOrPawn = 0;

	void Clear() {
		for (int x = 0; x < 10; x++)
			for (int y = 0; y < 12; y++)
				board[x + y * 10] = x > 0 && x < 9 && y>1 && y < 10 ? EMPTY : INVALID;
	}

	void Init() {
		int sq, pc;
		Clear();
		for (sq = 0; sq < 120; sq++)
			SetCastle[sq] = 0;
		SetCastle[21] = B_QS; SetCastle[28] = B_KS; SetCastle[25] = B_QS | B_KS;
		SetCastle[91] = W_QS; SetCastle[98] = W_KS; SetCastle[95] = W_QS | W_KS;
		for (pc = 0; pc < 8; pc++)
			for (sq = 0; sq < 120; sq++) {
				EvalSq[((pc | WHITE) << 7) + sq] = PieceValues[pc];
				EvalSq[((pc | BLACK) << 7) + sq] = -PieceValues[pc];
				if (pc == PAWN)
				{
					EvalSq[((pc | WHITE) << 7) + sq] += (9 - Rank(sq)) * Cent[File(sq)];
					EvalSq[((pc | BLACK) << 7) + sq] -= Rank(sq) * Cent[File(sq)];
				}
				else if (pc == KING) {}
				else {
					if (pc != ROOK && Rank(sq) == 8) EvalSq[((pc | WHITE) << 7) + sq] -= 8;
					if (pc != ROOK && Rank(sq) == 1) EvalSq[((pc | BLACK) << 7) + sq] += 8;
					EvalSq[((pc | WHITE) << 7) + sq] += CentEval[File(sq)];
					EvalSq[((pc | BLACK) << 7) + sq] -= CentEval[File(sq)];
				}
				EvalSq[(0 << 7) + sq] = (Rank(sq) - 9) * 2 + KingEval[File(sq)];
				EvalSq[(1 << 7) + sq] = (Rank(sq)) * 2 - KingEval[File(sq)];
				EvalSq[(2 << 7) + sq] = 2 * CentEval[File(sq)];
				EvalSq[(3 << 7) + sq] = -2 * CentEval[File(sq)];
			}
	}

	void SetFen(vector<string> fen) {
		Eval = 0;
		nMoves = 0;
		WMat = BMat = 0;
		EPsq = 0;
		Castling = 0xf;
		Clear();
		int sq = 21;
		string ele = fen[0];
		for (char c : ele)
			switch (c) {
			case 'p':Eval += EvalSq[((PAWN | BLACK) << 7) + sq]; board[sq] = PAWN | BLACK; Eval += EvalSq[(PAWN << 7) + sq]; sq++; break;
			case 'n':Eval += EvalSq[((KNIGHT | BLACK) << 7) + sq]; BMat += PieceValues[KNIGHT]; board[sq] = KNIGHT | BLACK; Eval += EvalSq[(KNIGHT << 7) + sq]; sq++; break;
			case 'b':Eval += EvalSq[((BISHOP | BLACK) << 7) + sq]; BMat += PieceValues[BISHOP]; board[sq] = BISHOP | BLACK; Eval += EvalSq[(BISHOP << 7) + sq]; sq++; break;
			case 'r':Eval += EvalSq[((ROOK | BLACK) << 7) + sq]; BMat += PieceValues[ROOK]; board[sq] = ROOK | BLACK; Eval += EvalSq[(ROOK << 7) + sq]; sq++; break;
			case 'q':Eval += EvalSq[((QUEEN | BLACK) << 7) + sq]; BMat += PieceValues[QUEEN]; board[sq] = QUEEN | BLACK; Eval += EvalSq[(QUEEN << 7) + sq]; sq++; break;
			case 'k':Eval += EvalSq[((KING | BLACK) << 7) + sq]; BKsq = sq;  board[sq] = KING | BLACK; sq++; Eval += EvalSq[(KING << 7) + sq]; break;
			case 'P':Eval += EvalSq[((PAWN | WHITE) << 7) + sq]; board[sq] = PAWN | WHITE; Eval += EvalSq[(PAWN << 7) + sq]; sq++; break;
			case 'N':Eval += EvalSq[((KNIGHT | WHITE) << 7) + sq]; WMat += PieceValues[KNIGHT]; board[sq] = KNIGHT | WHITE; Eval += EvalSq[(KNIGHT << 7) + sq]; sq++; break;
			case 'B':Eval += EvalSq[((BISHOP | WHITE) << 7) + sq]; WMat += PieceValues[BISHOP]; board[sq] = BISHOP | WHITE; Eval += EvalSq[(BISHOP << 7) + sq]; sq++; break;
			case 'R':Eval += EvalSq[((ROOK | WHITE) << 7) + sq]; WMat += PieceValues[ROOK]; board[sq] = ROOK | WHITE; Eval += EvalSq[(ROOK << 7) + sq]; sq++; break;
			case 'Q':Eval += EvalSq[((QUEEN | WHITE) << 7) + sq]; WMat += PieceValues[QUEEN]; board[sq] = QUEEN | WHITE; Eval += EvalSq[(QUEEN << 7) + sq]; sq++; break;
			case 'K':WKsq = sq; board[sq] = KING | WHITE; Eval += EvalSq[(KING << 7) + sq]; sq++; break;
			case '1': sq += 1; break;
			case '2': sq += 2; break;
			case '3': sq += 3; break;
			case '4': sq += 4; break;
			case '5': sq += 5; break;
			case '6': sq += 6; break;
			case '7': sq += 7; break;
			case '8': sq += 8; break;
			case '/': sq += 2; break;
			}

		ele = fen[1];
		color = (ele == "w") ? WHITE : BLACK;

		ele = fen[2];
		for (char c : ele)
			switch (c)
			{
			case 'K':
				Castling ^= W_KS;
				break;
			case 'Q':
				Castling ^= W_QS;
				break;
			case 'k':
				Castling ^= B_KS;
				break;
			case 'q':
				Castling ^= B_QS;
				break;
			}

		ele = fen[3];
		if (ele != "-")
		{
			int file = ele[0] - 'a';
			int rank = 7 - (ele[1] - '1');
			EPsq = SQ(file, rank);
		}
	}

	int CanCastleKS(const int Color) const {
		if (Color == WHITE && !(Castling & W_KS) && board[WKsq + 1] == EMPTY && !ColorAttacksSq(BLACK, WKsq + 1) && board[WKsq + 2] == EMPTY) return 1;
		if (Color == BLACK && !(Castling & B_KS) && board[BKsq + 1] == EMPTY && !ColorAttacksSq(WHITE, BKsq + 1) && board[BKsq + 2] == EMPTY) return 1;
		return 0;
	}

	int CanCastleQS(const int Color) const {
		if (Color == WHITE && !(Castling & W_QS) && board[WKsq - 1] == EMPTY && !ColorAttacksSq(BLACK, WKsq - 1) && board[WKsq - 2] == EMPTY && board[WKsq - 3] == EMPTY) return 1;
		if (Color == BLACK && !(Castling & B_QS) && board[BKsq - 1] == EMPTY && !ColorAttacksSq(BLACK, BKsq - 1) && board[BKsq - 2] == EMPTY && board[BKsq - 3] == EMPTY) return 1;
		return 0;
	}

	void AdjustMat(int Dst, const int Mul) {
		int pt = board[Dst] & 7;
		if (pt == PAWN) return;
		if (board[Dst] & WHITE)
			WMat += Mul * PieceValues[pt];
		else
			BMat += Mul * PieceValues[pt];
	}

	void MovePiece(const int Src, const int Dst, const int Promo) {
		int Piece = board[Src];
		Eval += EvalSq[(Piece << 7) + Dst] - EvalSq[(Piece << 7) + Src];
		if (board[Dst] != EMPTY)
		{
			Eval -= EvalSq[(board[Dst] << 7) + Dst];
			AdjustMat(Dst, -1);
		}
		board[Dst] = Piece;
		board[Src] = EMPTY;
		if (Piece == (KING | WHITE)) WKsq = Dst;
		if (Piece == (KING | BLACK)) BKsq = Dst;
		if ((Piece & 7) == PAWN) {
			if (Dst < 30 || Dst > 90) {
				board[Dst] += Promo + 1;
				AdjustMat(Dst, 1);
				Eval += EvalSq[(board[Dst] << 7) + Dst] - EvalSq[(Piece << 7) + Dst];
			}
			if (Dst == EPsq) {
				EPsq = Src + File(Dst) - File(Src);
				Eval -= EvalSq[(board[EPsq] << 7) + EPsq];
				board[EPsq] = EMPTY;
			}
			if (abs(Src - Dst) == 20) EPsq = ((Src + Dst) >> 1); else EPsq = 0;
		}
		else EPsq = 0;
	}

	void DoMove(const int Move) {
		int Dst = DST(Move), Src = SRC(Move);
		Castling |= SetCastle[Src] | SetCastle[Dst];
		nMoves++;
		color = SWITCH(color);
		if ((board[Src] & 7) == KING) {
			if (Dst == Src - 2) { MovePiece(Src, Src - 2, 0); MovePiece(Src - 4, Src - 1, 0); return; }
			if (Dst == Src + 2) { MovePiece(Src, Src + 2, 0); MovePiece(Src + 3, Src + 1, 0); return; }
		}
		MovePiece(Src, Dst, PROMO(Move));
	}

	int CheckDirec(int Sq, const int Dir, const int Piece1, const int Piece2) const {
		Sq += Dir;
		while (board[Sq] == EMPTY) Sq += Dir;
		if (board[Sq] == Piece1 || board[Sq] == Piece2) return 1; else	return 0;
	}

	int ColorAttacksSq(int Color, int Sq) const {
		int i;
		for (i = 0; i < 8; i++)
			if (board[Sq + N_dirs[i]] == (KNIGHT | Color))
				return 1;
		for (i = 0; i < 8; i++)
			if (board[Sq + K_dirs[i]] == (KING | Color))
				return 1;
		for (i = 0; i < 4; i++)
			if (CheckDirec(Sq, R_dirs[i], (QUEEN | Color), (ROOK | Color)))
				return 1;
		for (i = 0; i < 4; i++)
			if (CheckDirec(Sq, B_dirs[i], (QUEEN | Color), (BISHOP | Color)))
				return 1;
		int n = (Color == WHITE) ? 4 : 0;
		for (i = 2; i <= 3; i++)
			if (board[Sq + P_dirs[i + n]] == (PAWN | Color))
				return 1;
		return 0;
	}

	int IsCheck(int color) const {
		return (color == WHITE) ? ColorAttacksSq(BLACK, WKsq) : ColorAttacksSq(WHITE, BKsq);
	}

	int Evaluate() const {
		if (WMat < 1400 && BMat < 1400)
			return Eval + EvalSq[(2 << 7) + WKsq] + EvalSq[(3 << 7) + BKsq];
		return Eval + EvalSq[(0 << 7) + WKsq] + EvalSq[(1 << 7) + BKsq];
	}

}board;

struct SMovelist
{
	int m_Moves[256];
	int m_nMoves, m_nAttacks, m_bCaps;
	unsigned char* m_pSqs = NULL;

	void inline AddMove(int Src, int Dst) {
		if (m_bCaps) return;
		m_Moves[m_nMoves++] = Src + (Dst << 7) + (3 << 14) + (200 << 16);
	}

	void inline AddAtkMove(int Src, int Dst) {
		m_Moves[m_nMoves++] = Src + (Dst << 7) + (3 << 14) + ((200 + PieceValues[(m_pSqs[Dst] & 7)]) << 16);
	}

	void inline GenPieceMoves(const int MoveArray[], const int bSlide, const int nDirs, int Sq, SBoard& Board, const int COLOR) {
		for (int i = 0; i < nDirs; i++) {
			int tempSq = Sq + MoveArray[i];
			if (bSlide)
				while (Board.board[tempSq] == EMPTY) {
					AddMove(Sq, tempSq);
					tempSq += MoveArray[i];
				}
			if (Board.board[tempSq] & SWITCH(COLOR)) AddAtkMove(Sq, tempSq);
			else if (Board.board[tempSq] == EMPTY)	AddMove(Sq, tempSq);
		}
	}

	void inline GenPawnMoves(const int MoveArray[], int Sq, SBoard& Board, const int COLOR) {
		int n = (COLOR == BLACK) ? 4 : 0;
		if (Board.board[Sq + P_dirs[n]] == EMPTY) {
			int rank = RelativeRank(Sq, COLOR);
			AddMove(Sq, Sq + P_dirs[n]);
			if (rank == 2 && Board.board[Sq + P_dirs[n + 1]] == EMPTY)
				AddMove(Sq, Sq + P_dirs[n + 1]);
		}
		if (Sq + P_dirs[n + 2] == Board.EPsq || (Board.board[Sq + P_dirs[n + 2]] & SWITCH(COLOR))) AddAtkMove(Sq, Sq + P_dirs[n + 2]);
		if (Sq + P_dirs[n + 3] == Board.EPsq || (Board.board[Sq + P_dirs[n + 3]] & SWITCH(COLOR))) AddAtkMove(Sq, Sq + P_dirs[n + 3]);
	}

	void Generate(SBoard& Board, int bCaps) {
		m_nMoves = 0;
		m_bCaps = bCaps;
		m_pSqs = Board.board;
		int Color = Board.color;
		for (int Sq = 20; Sq < 100; Sq++)
			switch (Board.board[Sq] ^ Color) {
			case PAWN: GenPawnMoves(P_dirs, Sq, Board, Color); break;
			case KNIGHT: GenPieceMoves(N_dirs, 0, 8, Sq, Board, Color); break;
			case BISHOP: GenPieceMoves(B_dirs, 1, 4, Sq, Board, Color); break;
			case ROOK: GenPieceMoves(R_dirs, 1, 4, Sq, Board, Color); break;
			case QUEEN: GenPieceMoves(Q_dirs, 1, 8, Sq, Board, Color); break;
			case KING: GenPieceMoves(K_dirs, 0, 8, Sq, Board, Color);
				if (!Board.IsCheck(Color)) {
					if (Board.CanCastleQS(Color)) AddMove(Sq, Sq - 2);
					if (Board.CanCastleKS(Color)) AddMove(Sq, Sq + 2);
				}
				break;
			};
	}

	void ScoreMoves(SBoard& Board, const int Color, int BestMove) {
		for (int i = 0; i < m_nMoves; i++) {
			int Dst = DST(m_Moves[i]);
			int Src = SRC(m_Moves[i]);
			int Piece = Board.board[Src];
			if (Color == WHITE) m_Moves[i] += ((EvalSq[(Piece << 7) + Dst] - EvalSq[(Piece << 7) + Src]) << 16);
			if (Color == BLACK) m_Moves[i] -= ((EvalSq[(Piece << 7) + Dst] - EvalSq[(Piece << 7) + Src]) << 16);
			if ((m_Moves[i] & 65535) == (BestMove & 65535))
				m_Moves[i] += (2048 << 16);
		}
	}

	int GetNextMove(int& nMove) {
		int Max = -1, Next = -1;
		for (int i = 0; i < m_nMoves; i++)
			if (m_Moves[i] && VALUE(m_Moves[i]) > Max) {
				nMove = m_Moves[i];
				Next = i;
				Max = VALUE(nMove);
			}
		if (Next == -1) return 0;
		m_Moves[Next] = 0;
		return 1;
	}

};

U64 RepNum[2000];

int inline static Repetition(const U64 HashKey, int start, int ahead) {
	int i = (start > 0) ? start : 0;
	if ((i & 1) != (ahead & 1)) i++;
	for (; i < ahead; i += 2)
		if (RepNum[i] == HashKey)
			return true;
	return false;
}

void inline static AddRepBoard(const U64 HashKey, int ahead) {
	RepNum[ahead] = HashKey;
}

U64 HashFunction[128][16], HashSTM;
struct TEntry {
	U64 m_checksum;
	short m_eval, m_bestmove;
	char  m_depth, m_failtype, m_ahead;

	void inline Read(U64 CheckSum, short alpha, short beta, int& bestmove, int& value, int depth, int ahead) const {
		if (m_checksum == CheckSum) {
			if (m_depth >= depth) {
				int tempVal = m_eval;
				if (abs(m_eval) > 18000) {
					if (m_eval > 0) tempVal = m_eval - ahead + m_ahead;
					if (m_eval < 0) tempVal = m_eval + ahead - m_ahead;
				}
				switch (m_failtype) {
				case 0: value = tempVal; break;
				case 1: if (tempVal <= alpha) value = tempVal; 	break;
				case 2: if (tempVal >= beta) value = tempVal;	break;
				}
			}
			if (depth > 2) bestmove = m_bestmove;
		}
	}
	void inline Write(U64 CheckSum, short alpha, short beta, int& bestmove, int& value, int depth, int ahead) {
		m_checksum = CheckSum;
		m_eval = value;
		m_ahead = ahead;
		m_depth = depth;
		m_bestmove = (bestmove & 0xffff);
		if (value <= alpha) m_failtype = 1; else if (value >= beta)  m_failtype = 2; else m_failtype = 0;
	}

	static U64 rand64() {
		static U64 next = 1;
		next = next * 1103515245 + 12345;
		return next;
	}

	static void Create_HashFunction() {
		for (int i = 0; i < 128; i++)
			for (int x = 0; x < 16; x++) {
				HashFunction[i][x] = rand64();
			}
		HashSTM = HashFunction[0][0];
	}

	static U64 HashBoard(const SBoard& Board) {
		U64 CheckSum = 0;
		for (int index = 21; index <= 99; index++) {
			int nPiece = Board.board[index];
			if (nPiece == INVALID) continue;
			if (nPiece != EMPTY) CheckSum ^= HashFunction[index][(nPiece & 15)];
		}
		if (Board.color == BLACK) CheckSum ^= HashSTM;
		return CheckSum;
	}
};

TEntry tt[HASH_SIZE] = {};
__int64 g_Nodes, g_CheckNodes;
int g_max_depth = 100;
int g_max_time;
clock_t g_start;

static void TTClear() {
	std::memset(tt, 0, sizeof(TEntry) * HASH_SIZE);
}

static int TTPermill()
{
	int pm = 0;
	for (int n = 0; n < 1000; n++)
		if (tt[n].m_checksum)
			pm++;
	return pm;
}

static string GetPv(SBoard& inBoard, int move, int ahead) {
	SMovelist Moves = {};
	SBoard board = {};
	board = inBoard;
	string uci = MoveToUci(move);
	board.DoMove(move);
	U64 n64Hash = TEntry::HashBoard(board);
	TEntry entry = tt[n64Hash % HASH_SIZE];
	if (entry.m_ahead < ahead)
		return uci;
	if (!entry.m_bestmove)
		return uci;
	string hashMove = MoveToUci(entry.m_bestmove);
	Moves.Generate(board, 0);
	for (int i = 0; i < Moves.m_nMoves; i++)
		if (MoveToUci(Moves.m_Moves[i]) == hashMove)
			return uci + " " + GetPv(board, entry.m_bestmove, ++ahead);
	return uci;
}

static void PrintPv(SBoard& board, int move, int Depth, int Eval, __int64 Nodes)
{
	string score = Eval > 19000 ? "mate " + to_string(((MATE_VALUE - Eval) >> 1) + 1) : Eval < -19000 ? "mate " + to_string((-MATE_VALUE - Eval) >> 1) : "cp " + to_string(Eval);
	cout << "info depth " << Depth << " score " << score << " time " << (clock() - g_start) << " nodes " << Nodes << " hashfull " << TTPermill() << " pv " << GetPv(board, move, 0) << endl;
}

static void PrintBestMove(int move) {
	cout << "bestmove " << MoveToUci(move) << endl;
}

static int SearchAlpha(SBoard& InBoard, int alpha, int beta, int depth, int ply, int& BestMove, int bNull)
{
	SMovelist Moves = {};
	SBoard Board = {};
	int Color = InBoard.color, Eval, NextBest = 0, nMove, bInCheck = InBoard.IsCheck(Color);
	U64 n64Hash = 0;
	if (depth > g_max_depth)
		return TIME;
	if (g_Nodes > g_CheckNodes) {
		g_CheckNodes = g_Nodes + 10000;
		if (g_max_time && (clock() - g_start) > g_max_time) return TIME;
	}
	if (!bInCheck && depth <= 0) {
		Eval = (InBoard.color == WHITE) ? InBoard.Evaluate() : -InBoard.Evaluate();
		if (Eval > alpha)
			alpha = Eval;
		if (alpha >= beta)
			return beta;
		Moves.Generate(InBoard, 1);
	}
	else {
		if (bNull && depth > 2 && !bInCheck
			&& ((Color == WHITE && InBoard.WMat > 400) || (Color == BLACK && InBoard.BMat > 400))) {
			InBoard.color = SWITCH(InBoard.color);
			Eval = -SearchAlpha(InBoard, -beta, -beta + 1, depth - 3, ply, NextBest, false);
			InBoard.color = SWITCH(InBoard.color);
			if (Eval == -TIME)
				return TIME;
			if (Eval >= beta)
				return beta;
		}
		Moves.Generate(InBoard, 0);
	}

	if (BestMove < 100 && depth > 2) {
		Eval = SearchAlpha(InBoard, alpha, beta, depth - 2, ply + 1, BestMove, true);
		if (Eval == TIME) return TIME;
	}
	Moves.ScoreMoves(InBoard, Color, BestMove);

	BestMove = 0;
	while (Moves.GetNextMove(nMove)) {
		Board = InBoard;
		Board.DoMove(nMove);
		g_Nodes++;
		if (Board.IsCheck(Color)) continue;
		NextBest = 0;
		Eval = -32000;
		if (depth > 1) {
			n64Hash = TEntry::HashBoard(Board);
			if (Repetition(n64Hash, Board.nMoves - 40, Board.nMoves)) Eval = 0;
			else {
				AddRepBoard(n64Hash, Board.nMoves);
				tt[n64Hash % HASH_SIZE].Read(n64Hash, alpha, beta, NextBest, Eval, depth - 1, ply);
			}
		}
		if (Eval == -32000)
		{
			Eval = -SearchAlpha(Board, -beta, -alpha, (bInCheck) ? (depth) : (depth - 1), ply + 1, NextBest, true);
			if (Eval == -TIME) return TIME;
		}
		if (depth > 1)
			tt[n64Hash % HASH_SIZE].Write(n64Hash, alpha, beta, NextBest, Eval, depth - 1, ply);
		if (Eval > alpha) {
			if (ply == 0)
				PrintPv(board, nMove, depth, Eval, g_Nodes);
			BestMove = nMove;
			alpha = Eval;
			if (alpha >= beta) return beta;
		}
		if (BestMove == 0) BestMove = 1;
	}

	if (!Moves.m_bCaps && BestMove == 0)
		return (bInCheck) ? ply - MATE_VALUE : 0;
	return alpha;
}

static void SearchIteratively(SBoard& board, int& move, int& eval) {
	g_Nodes = 0;
	g_CheckNodes = g_Nodes + 10000;
	g_start = clock();
	int SearchEval, SearchMove;
	for (int depth = 1; depth <= g_max_depth; depth++) {
		SearchEval = SearchAlpha(board, -MATE_VALUE, MATE_VALUE, depth, 0, SearchMove, false);
		if (SearchEval != TIME)
			eval = SearchEval;
		if (SearchMove > 100)
			move = SearchMove;
		if (g_max_time && ((clock() - g_start) > (g_max_time / 2)))
			break;
		if (abs(eval) >= (MATE_VALUE - depth))
			break;
	}
}

static int UciToMove(string s) {
	if (s[0] < 'a' || s[0] > 'h' || s[1] < '0' || s[1] > '9' || s[2] < 'a' || s[2] > 'h' || s[3] < '0' || s[3] > '9') return -1;
	int Src = SQ(s[0] - 'a', 7 - (s[1] - '1')), Dst = SQ(s[2] - 'a', 7 - (s[3] - '1')), Upgrade = 3;
	if (s[4] == 'n' || s[4] == 'N') Upgrade = 0;
	if (s[4] == 'b' || s[4] == 'B') Upgrade = 1;
	if (s[4] == 'r' || s[4] == 'R') Upgrade = 2;
	return Src + (Dst << 7) + (Upgrade << 14);
}

static vector<string> SplitString(string s) {
	vector<string> words;
	istringstream iss(s);
	string word;
	while (iss >> word)
		words.push_back(word);
	return words;
}

static int GetInt(vector<string> vs, string name, int def) {
	bool r = false;
	for (string s : vs) {
		if (r) return stoi(s);
		r = s == name;
	}
	return def;
}

static void PrintBoard() {
	int r, f, sq;
	string uw = "ANBRQKXX";
	string ub = "anbrqkxx";
	string s = "   +---+---+---+---+---+---+---+---+";
	string t = "     A   B   C   D   E   F   G   H";
	cout << t << endl;
	for (r = 7; r >= 0; r--) {
		cout << s << endl;
		cout << " " << r + 1 << " |";
		for (f = 0; f <= 7; f++) {
			sq = SQ(f, 7 - r);
			int piece = board.board[sq];
			if (!piece)
				cout << "   |";
			else if (piece & WHITE)
				cout << " " << uw[piece & 0x7] << " |";
			else if (piece & BLACK)
				cout << " " << ub[piece & 0x7] << " |";
		}
		cout << endl;
	}
	cout << s << endl;
	cout << t << endl;
}

static void ParsePosition(vector<string> commands) {
	vector<string> fen = {};
	vector<string> moves = {};
	int mark = 0;
	for (int i = 1; i < commands.size(); i++) {
		if (mark == 1)
			fen.push_back(commands[i]);
		if (mark == 2)
			moves.push_back(commands[i]);
		if (commands[i] == "fen")
			mark = 1;
		else if (commands[i] == "moves")
			mark = 2;
	}
	if (fen.size() != 6)
		fen = SplitString(defFen);
	board.SetFen(fen);
	for (string m : moves)
	{
		int move = UciToMove(m);
		board.DoMove(move);
		AddRepBoard(TEntry::HashBoard(board), board.nMoves);
	}
}

static void UciLoop() {
	const int size = 4000;
	char line[size] = {};
	int move = 1, eval = 0, inc = 0;
	board.Init();
	board.SetFen(SplitString(defFen));
	while (true) {
		if (!fgets(line, size, stdin)) return;
		vector<string> commands = SplitString(line);
		if (!commands.size())
			continue;
		if (commands[0] == "uci") {
			cout << "id name " << NAME << endl;
			cout << "uciok" << endl;
		}
		else if (commands[0] == "isready")
			cout << "readyok" << endl;
		else if (commands[0] == "ucinewgame")
			TTClear();
		else if (commands[0] == "print")
			PrintBoard();
		else if (commands[0] == "position")
			ParsePosition(commands);
		else if (commands[0] == "go") {
			g_max_depth = GetInt(commands, "depth", 0xff);
			g_max_time = GetInt(commands, board.color == WHITE ? "wtime" : "btime", 0) / 30;
			if (!g_max_time)
				g_max_time = GetInt(commands, "movetime", 0xffffff);
			move = 0;
			SearchIteratively(board, move, eval);
			if (move) {
				PrintBestMove(move);
				board.DoMove(move);
				AddRepBoard(TEntry::HashBoard(board), board.nMoves);
			}
		}
		else if (commands[0] == "test") {
			board.SetFen(SplitString("8/8/8/8/3K4/8/5Q2/3k4 w - - 20 199"));
		}
		else if (commands[0] == "quit")
			return;
	}
}

int main() {
	PrintWelcome();
	TEntry::Create_HashFunction();
	UciLoop();
}