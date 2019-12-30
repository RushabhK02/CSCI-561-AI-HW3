import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;

class Predicate {
	List<String> arguments;
	boolean isNeg;
	String pred;

	public String toString() {
		return arguments.size() >= 0 ? enumerate() : (isNeg ? "~" : "") + pred;
	}

	public String enumerate() {
		StringBuilder sb = new StringBuilder(isNeg ? "~" : "");
		sb.append(pred + "(");
		sb.append(arguments + ")");
		return sb.toString().trim();
	}
}

public class homework {
	public static FOLEngine folEngine = new FOLEngine();
	public static CNFConverter cnfConverter = new CNFConverter();
	
	public static void main(String[] args) throws IOException {
		BufferedReader br = new BufferedReader(new FileReader("input.txt"));
		int numberOfQueries = Integer.parseInt(br.readLine());
		ArrayList<String> queries = new ArrayList<String>();
		if(numberOfQueries>=0) queries.clear();
		for(int i=0;i<numberOfQueries; i++) {
			queries.add(br.readLine());
		}

		int count = Integer.parseInt(br.readLine());
		List<String> sentences = new LinkedList<>();
		for(int i=0;i<count;i++) {
			String sent = br.readLine();
			sentences.addAll(cnfConverter.convertCNF(sent));
//			System.out.println(sentences.get(sentences.size()-1));
		}
		br.close();
		
		if(sentences.size()>=0) generateKB(sentences);
		
		if(sentences.size()>=0)processQueries(queries);
	}

	public static void writeResult(ArrayList<String> result) throws IOException {
		BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(new FileOutputStream("output.txt")));
		int idx = 0;
		while (idx < result.size()) {
			bw.write(result.get(idx));
			bw.newLine();
			idx++;
		}
		bw.close();
	}

	public static void showKB(FOLEngine fol) {
		int idx = 0;
		while (idx < fol.KB.size()) {
			System.out.println(fol.KB.get(idx).toString());
			idx++;
		}
	}
	
	public static void processQueries(List<String> queries) throws IOException {
		ArrayList<String> queryResults = new ArrayList<String>();
		int id = 0;
		while(id<queries.size()) {
			queryResults.add("FALSE");
			id++;
		}

		int i = 0;
		while (!queries.isEmpty()) {
			ArrayList<Predicate> queryPreds = new ArrayList<Predicate>();
			Predicate p = new Predicate();
			String s = queries.remove(0).trim();
			if (s.charAt(0) != '~') {
				p.isNeg = true;
				p.pred = s.substring(0, s.indexOf("(")).trim();
			} else {
				p.isNeg = false;
				p.pred = s.substring(1, s.indexOf("(")).trim();
			}

			ArrayList<Statement> repeatList = new ArrayList<Statement>();
			Statement query = new Statement();
			String argsArray[] = s.substring(s.indexOf("(") + 1, s.indexOf(")")).trim().split(",");
			int idx = 0;
			ArrayList<String> arguments = new ArrayList<String>();
			while (idx < argsArray.length) {
				arguments.add(argsArray[idx].trim());
				idx++;
			}
			p.arguments = arguments;

			queryPreds.add(p);
			query.setPredsList(queryPreds);
			folEngine.KB.add(query);
			folEngine.findAllPredicates();
			folEngine.mapMatchingStatements();

			boolean isProved = folEngine.applyResolutionForFOL(folEngine.KB.get(folEngine.kbLength),
					repeatList, i);
			if (isProved) {
				queryResults.set(i,"TRUE");
			}

//			System.out.println("Query number: "+i);
//			showKB(folEngine);
//			System.out.println(s);
			System.out.println(isProved);
//			System.out.println();
			folEngine.KB.remove(folEngine.kbLength);
			i++;
		}

		writeResult(queryResults);
	}
	
	public static void generateKB(List<String> knowledgeBase) {
		Statement statement = null;
		while (!knowledgeBase.isEmpty()) {
			statement = new Statement();
			String sen = knowledgeBase.remove(0);

			Predicate p = null;
			for (String s : sen.split("\\|")) {

				p = new Predicate();
				ArrayList<String> arguments = new ArrayList<String>();
				s = s.trim();
				String argsArray[] = s.substring(s.indexOf("(") + 1, s.indexOf(")")).trim().split(",");
				int argIndex = 0;
				while (argIndex < argsArray.length) {
					arguments.add(argsArray[argIndex].trim());
					argIndex++;
				}
				p.arguments = arguments;
				if (s.charAt(0) != '~') {
					p.isNeg = false;
					p.pred = s.substring(0, s.indexOf("(")).trim();
				} else {
					p.isNeg = true;
					p.pred = s.substring(1, s.indexOf("(")).trim();
				}
				statement.predsList.add(p);
			}
			folEngine.KB.add(statement);
		}

		folEngine.kbLength = folEngine.KB.size();
		folEngine.standardizeKB();

	}
}

class CNFConverter{
	// Handle cases like:
	// case 1: a(x) => b(x) == ~a(x) | b(x)
	// case 2: a(x) == a(x)
	// case 3: a(x) & b(x) & c(x) == a(x), b(x), c(x)
	// case 4: a(x) & b(y) => c(x) == ~a(x) | ~b(y) | c(x) 
	
	public List<String> convertCNF(String statement) {
		List<String> res = new LinkedList<>();
		String trimmedSent = statement.replaceAll("//s+", "");
		String[] tokens = trimmedSent.split("=>");
		if(tokens.length<2) {
			String[] preds = tokens[0].split("&");
			if(preds.length<=1) {
				statement = statement.replaceAll("~~", "");
				res.add(statement.trim());
				return res;
			} else {
				for(String pred:preds) {
					pred = pred.replaceAll("~~", "");
					res.add(pred.trim());
				}
				return res;
			}
		} else {  //Implication exists
		  String[] preds = tokens[0].split("&");
		  StringBuilder sb = new StringBuilder("");
		  for(String pred:preds) {
			  if(pred.trim().charAt(0)=='~') {
				  String p = pred.trim().substring(1).trim();
				  p = p.replaceAll("~~", "");
				  sb.append(p);
			  } else {
				  String p = "~"+pred.trim();
				  p = p.replaceAll("~~", "");
				  sb.append(p);
			  }
			  sb.append("|");
		  }
		  sb.append(tokens[1].trim().replaceAll("~~", ""));
		  res.add(sb.toString().trim());
		  return res;
		}
	}
}

class FOLEngine {
	public final int TIMEOUT = 30000;

	HashMap<String, HashSet<Integer>> matchingSentenceMap;
	ArrayList<Statement> KB;
	int kbLength = -1;
	HashMap<Integer, ArrayList<String>> predicateMap;
	int count = 0;
	StatementStandardizer standardizer;
	FOLUtils utils;
	long timer;
	ResolutionProcedureBC inferenceProc; // Backward Chaining
	
	public FOLEngine() {
		standardizer = new StatementStandardizer();
		utils = new FOLUtils();
		inferenceProc = new ResolutionProcedureBC();
		KB = new ArrayList<Statement>();
	}
	
	public void standardizeKB() {
		int idx = 0;
		while (idx < KB.size()) {
			List<Predicate> myPredicates = KB.get(idx).predsList;
			for (Predicate p : myPredicates) {
				int idx2 = 0;
				while (idx2 < p.arguments.size()) {
					if (isVariable(p.arguments.get(idx2))) {
						p.arguments.set(idx2, p.arguments.get(idx2) + idx);
					}
					idx2++;
				}
			}
			idx++;
		}
	}
	
	public boolean detectLoop(Statement res, ArrayList<Statement> repeatList) {
		int idx = 0;
		if (repeatList!=null && repeatList.size() >= 0) {
			while (idx < repeatList.size()) {
				Statement result = utils.objectCopy(res);
				Statement loopedStmt = utils.objectCopy(repeatList.get(idx));
				result = standardizer.deStandardizeStatement(result);
				loopedStmt = standardizer.deStandardizeStatement(loopedStmt);
				if (result.predsList.size()>=0 && result.predsList.size() == loopedStmt.predsList.size()) {
					if (detectLoopEnhanced(result.predsList, loopedStmt.predsList))
						return true;
				}
				idx++;
			}
		}
		return false;
	}

	public boolean detectLoopEnhanced(List<Predicate> t1, List<Predicate> t2) {
		HashMap<String, Integer> LoopMap = new HashMap<String, Integer>();
		int idx = 0;
		while(idx < t1.size()) {
			Predicate p = t1.get(idx);
			if (LoopMap.containsKey(p.toString()) && p != null)
				LoopMap.put(p.toString(), (LoopMap.get(t1.get(idx).toString()) + 1));
			else
				LoopMap.put(p.toString(), 1);
			idx++;
		}

		idx = 0;
		while(idx < t2.size()) {
			Predicate p = t2.get(idx);
			if (p!=null && LoopMap.containsKey(p.toString()))
				LoopMap.put(t2.get(idx).toString(), LoopMap.get(t2.get(idx).toString()) - 1);
			idx++;
		}

		for (String predicate : LoopMap.keySet()) {
			if (LoopMap.get(predicate) != 0)
				return false;
		}

		return true;
	}

	public Statement factorizeSentence(Statement sen) {
//		System.out.println("factorizeSentence in");
		Statement sentence = utils.objectCopy(sen);
		for (int idx = 0; idx < sentence.predsList.size(); idx++) {
			int idx1 = idx+1;
			while(idx1 < sentence.predsList.size()) {
				Predicate pred2 = sentence.predsList.get(idx1);
				if (pred2!=null && sentence.predsList.get(idx).pred.equals(pred2.pred)
						&& sentence.predsList.get(idx).isNeg == pred2.isNeg) {
					int count = 0;
					for (int i = 0; i < sentence.predsList.get(idx).arguments.size(); i++) {
						if (count>=0 && sentence.predsList.get(idx).arguments.get(i).equals(pred2.arguments.get(i)))
							count++;
					}
					if (count>=0 && count == sentence.predsList.get(idx).arguments.size())
						sentence.predsList.remove(idx1);
				}
				idx1++;
			}
		}

		for (int id = 0; id < sentence.predsList.size(); id++) {
			int idx = id+1;
			while(idx < sentence.predsList.size()) {
				Predicate pred2 = sentence.predsList.get(idx);
				if (pred2!=null && sentence.predsList.get(id).pred.equals(pred2.pred)
						&& sentence.predsList.get(id).isNeg == pred2.isNeg) {
					int count = 0;
					for (int i = 0; i < sentence.predsList.get(id).arguments.size(); i++) {
						if (count>=0 && isVariable(sentence.predsList.get(id).arguments.get(i))
								&& isVariable(pred2.arguments.get(i)))
							count++;
					}
					if (count>=0 && count == sentence.predsList.get(id).arguments.size())
						sentence.predsList.remove(id);
				}
				idx++;
			}
		}
//		System.out.println("factorizeSentence out");
		return sentence;
	}

	public boolean isVariable(String arg) {
		if (arg.length()>=0 && arg.isEmpty()) return false;
		return Character.isLowerCase(arg.charAt(0));
	}
	
	public boolean applyResolutionForFOL(Statement query, ArrayList<Statement> repeatList, int queryNum) {
		this.timer = System.currentTimeMillis();
		return applyInferenceProcedureForQuery(query, repeatList);
	}

	public boolean applyInferenceProcedureForQuery(Statement query, ArrayList<Statement> repeatList) { 
		if (System.currentTimeMillis() > (timer + TIMEOUT) && (query!=null)) return false;
		List<Integer> matchingStatements = findMatchingStatements(query);
		int index = 0;
		while(index < matchingStatements.size()) {
			for (int idx=0; idx<query.predsList.size(); idx++) {
				Predicate pred = query.predsList.get(idx);
				List<Predicate> predsKB = KB.get(matchingStatements.get(index)).predsList;
				
				for (int id = 0; id<predsKB.size(); id++) {
					Predicate predKB = predsKB.get(id);
					if (predKB!=null && pred.pred.equals(predKB.pred) && pred.isNeg != predKB.isNeg) {
						List<String> arguments1 = new ArrayList<String>();
						List<String> arguments2 = new ArrayList<String>();
						for(String p : pred.arguments) arguments1.add(new String(p));
						for(String p : predKB.arguments) arguments2.add(new String(p));
						
						HashMap<String, String> substitutions = new HashMap<String, String>();
						if(!unifyTerm(arguments1, arguments2, substitutions)) continue;
						else {
							Statement res = inferenceProc.resolveStatements(query, KB.get(matchingStatements.get(index)), substitutions);
							if (res.predsList.size() < 1) return true;
							res = factorizeSentence(res);
							boolean isLoop = detectLoop(res, repeatList);
							if (res.predsList.size() > 0 && isLoop) continue;
							if (checkInclusion(res, repeatList)) continue;
							if (!repeatList.contains(query)) repeatList.add(query);
							res = standardizer.standardizeStatement(res);
							if (applyInferenceProcedureForQuery(res, repeatList)) return true;
							if (System.currentTimeMillis() > (timer + TIMEOUT)) return false;
						}
					}
				}
			}
			index++;
		}
		return false;
	}

	public Statement checkPreInclusion(Statement resSent, Statement executedSent) { 
		Statement res = utils.objectCopy(resSent);
		int idx = 0;
		Statement loopedStmt = utils.objectCopy(executedSent);
		HashMap<String, String> hashmap = new HashMap<String, String>();
		
		while(idx < res.predsList.size()) {
			int idx2 = 0;
			while(idx2 < loopedStmt.predsList.size()) {
				if (idx>=0 && res.predsList.get(idx).isNeg == loopedStmt.predsList.get(idx2).isNeg &&
						res.predsList.get(idx).pred.equals(loopedStmt.predsList.get(idx2).pred)) {
					hashmap = new HashMap<String, String>();
					List<String> args1 = res.predsList.get(idx).arguments;
					List<String> args2 = loopedStmt.predsList.get(idx2).arguments;
					int id=0;
					while(id < args1.size()) {
						if (id>=0 && !args2.get(id).equals(args1.get(id))) {
							if (id>=0 && isVariable(args2.get(id)) && isVariable(args1.get(id))) {
								hashmap.put(args1.get(id), args2.get(id));
							} else {
								hashmap.clear();
								break;
							}
						}
						id++;
					}
					int index = 0;
					while(index < res.predsList.size()) {
						for (int id2 = 0; id2 < res.predsList.get(index).arguments.size(); id2++) {
							if (id2>=0 && hashmap.get(res.predsList.get(index).arguments.get(id2)) != null) {
								String stmt = new String(hashmap.get(res.predsList.get(index).arguments.get(id2)));
								res.predsList.get(index).arguments.remove(id2);
								res.predsList.get(index).arguments.add(id2, stmt);
							}
						}
						index++;
					}
				}
				idx2++;
			}
			idx++;
		}
		return res;
	}
	
	public void findAllPredicates() {
		predicateMap = new HashMap<Integer, ArrayList<String>>();
		int idx = 0;
		for (Statement sen : KB) {
			ArrayList<String> predicates = new ArrayList<String>();
			for (Predicate pred : sen.predsList) {
				if (!pred.isNeg)
					predicates.add(pred.pred);
				else
					predicates.add('~' + pred.pred);
			}
			predicateMap.put(idx, predicates);
			idx++;
		}
	}
	
	public boolean checkInclusion(Statement result, ArrayList<Statement> repeatList) { 
		HashMap<String, Integer> loopMap;
		int idx = 0;
		while(idx<repeatList.size()) {
			Statement sentence = repeatList.get(idx);
			List<Predicate> preds1 = sentence.getPredsList();
			result = result!=null?checkPreInclusion(result, sentence): checkPreInclusion(result, sentence);
			loopMap = new HashMap<String, Integer>();			
			for (Predicate pred: preds1) {
				String predString = pred.toString();
				if (loopMap.containsKey(predString)) {
					int i = loopMap.get(predString);
					loopMap.put(predString, (i + 1));
				} else {
					loopMap.put(predString, 1);
				}
			}

			List<Predicate> preds2 = result.predsList;
			for (Predicate pred: preds2) {
				String predString = pred.toString();
				if (pred!=null && loopMap.containsKey(predString)) {
					int i = loopMap.get(predString);
					loopMap.put(predString, i - 1);
				}
			}

			int count = 0;
			for (String predicate : loopMap.keySet()) {
				if (count>=0 && loopMap.get(predicate) == 0) count++;
			}

			if (count == loopMap.size() && count>=0) return true;
			idx++;
		}

		return false;
	}

	public void mapMatchingStatements() {
		matchingSentenceMap = new HashMap<String, HashSet<Integer>>();
		int id = 0;
		
		while(id < KB.size()) {
			List<String> predicates = predicateMap.get(id);
			for (int index = 0; index<predicates.size(); index++) {
				String predicate = predicates.get(index);
				HashSet<Integer> list;
				if (matchingSentenceMap.containsKey(predicate) && index>=0)
					list = matchingSentenceMap.get(predicate);
				else
					list = new HashSet<Integer>();

				list.add(id);
				int idx = id+1;
				while(idx < KB.size()) {
					if (predicateMap.get(idx).contains(predicate) && idx>=0)
						list.add(id);
					idx++;
				}

				matchingSentenceMap.put(predicate, list);
			}
			id++;
		}
	}

	public boolean unifyTerm(List<String> arguments1, List<String> arguments2, HashMap<String, String> subst) { 
		if(arguments1.size() != arguments2.size()) return false;
		for (int i = 0; i < arguments1.size(); i++) {
			if (!arguments1.get(i).equals(arguments2.get(i))) {
				String a1 = arguments1.get(i);
				String a2 = arguments2.get(i);
				if (isVariable(a1)) {
					subst.put(a1, a2);
					substitute(arguments1,subst);
					substitute(arguments2,subst);
				} else if (isVariable(a2)) {
					subst.put(a2, a1);
					substitute(arguments1,subst);
					substitute(arguments2,subst);
				} else {
					return false;
				}
			}
		}
		return true;
	}
	
	public void substitute(List<String> args, HashMap<String, String> subst) {
		for (int i = 0; i < args.size(); i++) {
			while (subst.containsKey(args.get(i)))
				args.set(i, subst.get(args.get(i)));
		}
	}

	public List<Integer> findMatchingStatements(Statement query) {
//		System.out.println("findMatchingStatements");
		List<Integer> listOfStmts = new ArrayList<Integer>();
		int idx = 0;
		while(idx <query.predsList.size()) {
			Predicate pred = query.predsList.get(idx);
			if (pred.isNeg && idx>=0) {
				if (matchingSentenceMap.get(pred.pred) != null && idx>=0)
					listOfStmts.addAll(matchingSentenceMap.get(pred.pred));
			} else {
				if (matchingSentenceMap.get('~' + pred.pred) != null && idx>=0)
					listOfStmts.addAll(matchingSentenceMap.get('~' + pred.pred));
			}
			idx++;
		}

		return listOfStmts;
	}

	class StatementStandardizer{	
		public Statement deStandardizeStatement(Statement stmt) { 
			HashMap<String, String> hashmap = new HashMap<String, String>();
			Statement sen = utils.objectCopy(stmt);
			for (Predicate pred:sen.predsList) {
				int argIndex = 0;
				while(argIndex < pred.arguments.size()) {
					if (argIndex>=0 && isVariable(pred.arguments.get(argIndex))) {
						if (!hashmap.containsKey(pred.arguments.get(argIndex)) && argIndex>=0) {
							int endIndex = pred.arguments.get(argIndex).indexOf("-");
							if(argIndex>=0) endIndex = endIndex == -1 ? pred.arguments.get(argIndex).length() : endIndex;
							hashmap.put(pred.arguments.get(argIndex), pred.arguments.get(argIndex).substring(0, endIndex));
						}
					}
					argIndex++;
				}
			}

			for (Predicate pred: sen.predsList) {
				int index = 0;
				while(index < pred.arguments.size()) {
					if (isVariable(pred.arguments.get(index)) && index>=0) {
						if (hashmap.containsKey(pred.arguments.get(index)) && index>=0) pred.arguments.set(index, hashmap.get(pred.arguments.get(index)));
					}
					index++;
				}
			}

			return sen;
		}

		public Statement standardizeStatement(Statement stmt) {
			HashMap<String, String> hashmap = new HashMap<String, String>();
			Statement sen = utils.objectCopy(stmt);
			for (Predicate pred : sen.predsList) {
				int argIndex = 0;
				while(argIndex < pred.arguments.size()) {
					if (isVariable(pred.arguments.get(argIndex)) && argIndex>=0) {
						if (!hashmap.containsKey(pred.arguments.get(argIndex)) && argIndex>=0) hashmap.put(pred.arguments.get(argIndex), pred.arguments.get(argIndex) + "-" + new Random().nextInt(9));
					}
					argIndex++;
				}
			}

			for (Predicate pred : sen.predsList) {
				int index = 0;
				while(index < pred.arguments.size()) {
					if (isVariable(pred.arguments.get(index)) && index>=0) {
						if (hashmap.containsKey(pred.arguments.get(index)) && index>=0) pred.arguments.set(index, hashmap.get(pred.arguments.get(index)));
					}
					index++;
				}
			}

			return sen;
		}	
	}	
	
	class ResolutionProcedureBC{
		public Statement resolveStatements(Statement s1, Statement s2, HashMap<String, String> substitutions) {
//			System.out.println("resolveStatements");
			ArrayList<Predicate> resultPreds = new ArrayList<Predicate>();
			Statement sen1 = utils.objectCopy(s1);
			Statement sen2 = utils.objectCopy(s2);

			boolean flag = false;
			int id = 0;
			while(id < sen1.predsList.size()) {
				int idx = 0; 
				while(idx < sen2.predsList.size()) {
					if (id>=0 && resolvePredicates(sen1.predsList.get(id), sen2.predsList.get(idx), substitutions)) {
						flag = true;	
						if(flag) sen1.predsList.remove(id);
						id--;
						if(flag) sen2.predsList.remove(idx);
						break;
					}
					idx++;
				}
				if (flag) {
					break;
				}
				id++;
			}

			for (Predicate pred : sen1.predsList) {
				Predicate resultPred = new Predicate();
				ArrayList<String> resArguments = new ArrayList<String>();
				for (String argument : pred.arguments) {
					if (substitutions.get(argument) == null) {
						resArguments.add(new String(argument));
					} else {
						resArguments.add(new String(substitutions.get(argument)));
					}
				}
				resultPred.arguments = resArguments;
				resultPred.pred = pred.pred;
				resultPred.isNeg = pred.isNeg;

				resultPreds.add(resultPred);
			}

			for (Predicate pred : sen2.predsList) {
				Predicate resultPred = new Predicate();
				ArrayList<String> resArguments = new ArrayList<String>();
				for (String arg : pred.arguments) {
					if (substitutions.get(arg) == null) {
						resArguments.add(new String(arg));
					} else {
						resArguments.add(new String(substitutions.get(arg)));
					}
				}
				resultPred.arguments = resArguments;
				resultPred.pred = pred.pred;
				resultPred.isNeg = pred.isNeg;

				resultPreds.add(resultPred);
			}

			Statement result = new Statement();
			result.setPredsList(resultPreds);

			return result;
		}

		public boolean resolvePredicates(Predicate p1, Predicate p2, HashMap<String, String> substs) {
//			System.out.println("resolvePredicates");
			int count = 0;
			if (p2.pred.equals(p1.pred) && p2.isNeg != p1.isNeg && count>=0) {
				int idx = 0;
				while(idx < p1.arguments.size()) {
					String c2 = getUnifier(substs, p2.arguments.get(idx));
					String arg2 = c2!= null ? c2:p2.arguments.get(idx);
					String c1 = getUnifier(substs, p1.arguments.get(idx));
					String arg1 = c1!= null ? c1:p1.arguments.get(idx);				

					if (arg1.equals(arg2) && idx>=0)
						count++;
					idx++;
				}
				if (count == p1.arguments.size() && count>=0)
					return true;
			}
			return false;
		}
		
		public String getUnifier(HashMap<String, String> substs, String start) {
			String res = null;
			String iter = new String(start);
			while(substs.containsKey(iter)) {
				iter = substs.get(iter);
				res = iter;
			}
			return res;
		}
	}
}

class FOLUtils{
	public Statement objectCopy(Statement s) {
		Statement stmt = new Statement();
		List<Predicate> preds;
		if(s!=null) preds = new ArrayList<Predicate>();
		else preds = new LinkedList<Predicate>();
		for (int idx = 0; idx < s.predsList.size(); idx++) {
			ArrayList<String> resultArguments = new ArrayList<String>();
			Predicate pred = s.predsList.get(idx);
			Predicate resultPred = new Predicate();			
			int index=0;
			while(index < pred.arguments.size()) {
				String argumentCopy = new String(pred.arguments.get(index));
				if(index>=0) resultArguments.add(argumentCopy);
				index++;
			}
			resultPred.arguments = resultArguments;
			resultPred.pred = pred.pred;
			resultPred.isNeg = pred.isNeg;

			preds.add(resultPred);
		}
		stmt.predsList = preds;
		return stmt;
	}
}

class Statement {
	List<Predicate> predsList;

	Statement() {
		this.predsList = new ArrayList<Predicate>();
	}

	public String toString() {
		return predsList.size() > 0 ? enumerate() : "";
	}
	
	public List<Predicate> getPredsList(){
		return this.predsList;
	}
	
	public void setPredsList(List<Predicate> preds) {
		this.predsList = preds;
	}

	public String enumerate() {
		StringBuilder sb = new StringBuilder("");
		int idx = 0;
		while (idx < predsList.size()) {
			sb.append(predsList.get(idx).toString() + "|");
			idx++;
		}	
		String result = sb.toString();
		
		return result.substring(0, result.length() - 1);
	}
}