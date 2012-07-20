package de.intranda.goobi.plugins.utils;

import java.io.File;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.jdom.Document;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.input.SAXBuilder;
import org.jdom.output.XMLOutputter;

/**
 * Extracts unique datafield elements from all MarcLoss files in the given folder and writes them into a new XML file.
 */
public class LossParser {

	private static String path = "/opt/digiverso/logs/CSIC";

	private static FilenameFilter lossFileFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("_MarcLoss.xml")) {
				validImage = true;
			}

			return validImage;
		}
	};

	private static Map<String, Element> existing = new HashMap<String, Element>();

	@SuppressWarnings("unchecked")
	public static void main(String[] args) {
		File dir = new File(path);
		if (dir.isDirectory()) {
			Document outDoc = new Document();
			outDoc.addContent(new Element("root"));
			File[] files = dir.listFiles(lossFileFilter);
			for (File f : files) {
				try {
					Document doc = new SAXBuilder().build(f);
					List<Element> dataFields = doc.getRootElement().getChildren("datafield", null);
					for (Element dataField : dataFields) {
						String tag = dataField.getAttributeValue("tag");
						String ind1 = dataField.getAttributeValue("ind1");
						String ind2 = dataField.getAttributeValue("ind2");
						String subfieldCode = dataField.getChild("subfield", null).getAttributeValue("code");
						String key = tag + "_" + ind1 + "_" + ind2 + "_" + subfieldCode;
						if (!existing.containsKey(key)) {
							existing.put(key, (Element) dataField.clone());
						}
					}
				} catch (JDOMException e) {
					e.printStackTrace();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}

			List<String> keys = new ArrayList<String>(existing.keySet());
			Collections.sort(keys);
			for (String key : keys) {
				outDoc.getRootElement().addContent(existing.get(key));
			}
			try {
				new XMLOutputter().output(outDoc, new FileWriter(new File(path, "loss.xml")));
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
}
